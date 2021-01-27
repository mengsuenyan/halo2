//! Gadget and chips for the [Sinsemilla] hash function.
//!
//! [Sinsemilla]: https://hackmd.io/iOw7-HpFQY6dPF1aFY8pAw

use std::fmt;

use crate::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::{Chip, Layouter},
    plonk::Error,
};

mod chip;
pub use chip::{SinsemillaChip, SinsemillaConfig};

/// Domain prefix used in SWU hash-to-curve to generate S_i's.
pub const S_DOMAIN_PREFIX: &str = "z.cash:SinsemillaS";

/// Domain prefix used in SWU hash-to-curve to generate Q.
pub const Q_DOMAIN_PREFIX: &str = "z.cash:SinsemillaQ";

/// Personalization input used to generate Q
/// TODO: Decide on personalization
pub const Q_PERSONALIZATION: [u8; 4] = [0u8; 4];

/// The set of circuit instructions required to use the [`Sinsemilla`] gadget.
pub trait SinsemillaInstructions<F: FieldExt, C: CurveAffine<Base = F>>: Chip<Field = F> {
    /// A message of at most `kn` bits.
    type Message: Clone + fmt::Debug;
    /// A message padded to `kn` bits.
    type PaddedMessage: Clone + fmt::Debug;
    /// The output of `Hash`.
    type HashOutput: fmt::Debug;

    /// Return Q
    fn q() -> (F, F);

    /// Pads the given message to `kn` bits.
    fn pad(
        layouter: &mut impl Layouter<Self>,
        message: Self::Message,
    ) -> Result<Self::PaddedMessage, Error>;

    /// Hashes the given message.
    ///
    /// TODO: Since the output is always curve point, maybe this should return
    /// `<Self as EccInstructions>::Point` instead of an associated type.
    fn hash(
        layouter: &mut impl Layouter<Self>,
        message: Self::PaddedMessage,
    ) -> Result<Self::HashOutput, Error>;
}

#[test]
fn test_sinsemilla() {
    use crate::arithmetic::FieldExt;
    use crate::circuit::{
        layouter::{self, RegionLayouter, RegionShape},
        Cell, Layouter, Permutation, Region,
    };
    use crate::pasta::{EpAffine, EqAffine, Fp};
    use crate::plonk::*;
    use crate::poly::commitment::Params;
    use crate::transcript::{Blake2bRead, Blake2bWrite};

    use std::{cmp, collections::HashMap, fmt, marker::PhantomData};

    /// This represents an advice column at a certain row in the ConstraintSystem
    #[derive(Copy, Clone, Debug)]
    pub struct Variable(Column<Advice>, usize);

    struct MyCircuit<F: FieldExt, C: CurveAffine<Base = F>> {
        _marker_f: PhantomData<F>,
        _marker_c: PhantomData<C>,
    }

    struct MyLayouter<'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F> + 'a> {
        cs: &'a mut CS,
        config: SinsemillaConfig<F, C>,
        regions: Vec<usize>,
        /// Stores the first empty row for each column.
        columns: HashMap<Column<Any>, usize>,
        _marker: PhantomData<F>,
    }

    impl<'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F> + 'a> fmt::Debug
        for MyLayouter<'a, F, C, CS>
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("MyLayouter")
                .field("config", &self.config)
                .field("regions", &self.regions)
                .field("columns", &self.columns)
                .finish()
        }
    }

    impl<'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F>> MyLayouter<'a, F, C, CS> {
        fn new(cs: &'a mut CS, config: SinsemillaConfig<F, C>) -> Result<Self, Error> {
            let mut res = MyLayouter {
                cs,
                config,
                regions: vec![],
                columns: HashMap::default(),
                _marker: PhantomData,
            };

            SinsemillaChip::load(&mut res)?;

            Ok(res)
        }
    }

    impl<'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F> + 'a>
        Layouter<SinsemillaChip<F, C>> for MyLayouter<'a, F, C, CS>
    {
        type Root = Self;

        fn config(&self) -> &SinsemillaConfig<F, C> {
            &self.config
        }

        fn assign_region<A, N, NR>(&mut self, name: N, mut assignment: A) -> Result<(), Error>
        where
            A: FnMut(Region<'_, SinsemillaChip<F, C>>) -> Result<(), Error>,
            N: Fn() -> NR,
            NR: Into<String>,
        {
            let region_index = self.regions.len();

            // Get shape of the region.
            let mut shape = RegionShape::new(region_index);
            {
                let region: &mut dyn RegionLayouter<SinsemillaChip<F, C>> = &mut shape;
                assignment(region.into())?;
            }

            // Lay out this region. We implement the simplest approach here: position the
            // region starting at the earliest row for which none of the columns are in use.
            let mut region_start = 0;
            for column in shape.columns() {
                region_start =
                    cmp::max(region_start, self.columns.get(column).cloned().unwrap_or(0));
            }
            self.regions.push(region_start);

            // Update column usage information.
            for column in shape.columns() {
                self.columns
                    .insert(*column, region_start + shape.row_count());
            }

            self.cs.enter_region(name);
            let mut region = MyRegion::new(self, region_index);
            {
                let region: &mut dyn RegionLayouter<SinsemillaChip<F, C>> = &mut region;
                assignment(region.into())?;
            }
            self.cs.exit_region();

            Ok(())
        }

        fn get_root(&mut self) -> &mut Self::Root {
            self
        }

        fn push_namespace<NR, N>(&mut self, name_fn: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
            self.cs.push_namespace(name_fn)
        }

        fn pop_namespace(&mut self, gadget_name: Option<String>) {
            self.cs.pop_namespace(gadget_name)
        }
    }

    struct MyRegion<'r, 'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F> + 'a> {
        layouter: &'r mut MyLayouter<'a, F, C, CS>,
        region_index: usize,
    }

    impl<'r, 'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F> + 'a> fmt::Debug
        for MyRegion<'r, 'a, F, C, CS>
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("MyRegion")
                .field("layouter", &self.layouter)
                .field("region_index", &self.region_index)
                .finish()
        }
    }

    impl<'r, 'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F> + 'a>
        MyRegion<'r, 'a, F, C, CS>
    {
        fn new(layouter: &'r mut MyLayouter<'a, F, C, CS>, region_index: usize) -> Self {
            MyRegion {
                layouter,
                region_index,
            }
        }
    }

    impl<'r, 'a, F: FieldExt, C: CurveAffine<Base = F>, CS: Assignment<F> + 'a>
        layouter::RegionLayouter<SinsemillaChip<F, C>> for MyRegion<'r, 'a, F, C, CS>
    {
        fn assign_advice<'v>(
            &'v mut self,
            annotation: &'v (dyn Fn() -> String + 'v),
            column: Column<Advice>,
            offset: usize,
            to: &'v mut (dyn FnMut() -> Result<F, Error> + 'v),
        ) -> Result<Cell, Error> {
            self.layouter.cs.assign_advice(
                annotation,
                column,
                self.layouter.regions[self.region_index] + offset,
                to,
            )?;

            Ok(Cell {
                region_index: self.region_index,
                row_offset: offset,
                column: column.into(),
            })
        }

        fn assign_fixed<'v>(
            &'v mut self,
            annotation: &'v (dyn Fn() -> String + 'v),
            column: Column<Fixed>,
            offset: usize,
            to: &'v mut (dyn FnMut() -> Result<F, Error> + 'v),
        ) -> Result<Cell, Error> {
            self.layouter.cs.assign_fixed(
                annotation,
                column,
                self.layouter.regions[self.region_index] + offset,
                to,
            )?;

            Ok(Cell {
                region_index: self.region_index,
                row_offset: offset,
                column: column.into(),
            })
        }

        fn constrain_equal(
            &mut self,
            permutation: &Permutation,
            left: Cell,
            right: Cell,
        ) -> Result<(), Error> {
            let left_column = permutation
                .mapping
                .iter()
                .position(|c| c == &left.column)
                .ok_or(Error::SynthesisError)?;
            let right_column = permutation
                .mapping
                .iter()
                .position(|c| c == &right.column)
                .ok_or(Error::SynthesisError)?;

            self.layouter.cs.copy(
                permutation.index,
                left_column,
                self.layouter.regions[left.region_index] + left.row_offset,
                right_column,
                self.layouter.regions[right.region_index] + right.row_offset,
            )?;

            Ok(())
        }
    }

    impl<F: FieldExt, C: CurveAffine<Base = F>> Circuit<F> for MyCircuit<F, C> {
        type Config = SinsemillaConfig<F, C>;

        fn configure(meta: &mut ConstraintSystem<F>) -> SinsemillaConfig<F, C> {
            SinsemillaChip::configure(meta, 11, 2)
        }

        fn synthesize(
            &self,
            cs: &mut impl Assignment<F>,
            config: SinsemillaConfig<F, C>,
        ) -> Result<(), Error> {
            let mut layouter = MyLayouter::new(cs, config)?;

            let message = vec![
                true, false, true, true, false, true, true, false, true, true, false, true,
            ];
            let message = SinsemillaChip::pad(&mut layouter, message)?;
            SinsemillaChip::hash(&mut layouter, message)?;

            Ok(())
        }
    }

    // Initialize the polynomial commitment parameters
    let k = 11;
    let params: Params<EqAffine> = Params::new(k);
    let empty_circuit: MyCircuit<Fp, EpAffine> = MyCircuit {
        _marker_f: PhantomData,
        _marker_c: PhantomData,
    };

    // Initialize the proving key
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    let circuit: MyCircuit<Fp, EpAffine> = MyCircuit {
        _marker_f: PhantomData,
        _marker_c: PhantomData,
    };

    // Create a proof
    let mut transcript = Blake2bWrite::init(vec![]);
    create_proof(&params, &pk, &[circuit], &[&[]], &mut transcript)
        .expect("proof generation should not fail");
    let proof: Vec<u8> = transcript.finalize();

    let msm = params.empty_msm();
    let mut transcript = Blake2bRead::init(&proof[..]);
    let guard = verify_proof(&params, pk.get_vk(), msm, &[&[]], &mut transcript).unwrap();
    let msm = guard.clone().use_challenges();
    assert!(msm.eval());
}
