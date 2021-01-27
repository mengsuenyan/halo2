use super::super::S_DOMAIN_PREFIX;
use super::SinsemillaChip;
use crate::{
    arithmetic::{Curve, CurveAffine, FieldExt},
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use std::marker::PhantomData;

/// Inputs to a lookp argument involving GeneratorTable
#[derive(Clone, Debug)]
pub(super) struct GeneratorInputs {
    m: Column<Advice>,
    x_p: Column<Advice>,
    y_p: Column<Advice>,
}

/// Table containing independent generators P[0..2^k]
#[derive(Clone, Debug)]
pub(super) struct GeneratorTable<F: FieldExt, C: CurveAffine<Base = F>> {
    k: usize,
    table_idx: Column<Fixed>,
    table_x: Column<Fixed>,
    table_y: Column<Fixed>,
    _marker_f: PhantomData<F>,
    _marker_c: PhantomData<C>,
}

impl<F: FieldExt, C: CurveAffine<Base = F>> GeneratorTable<F, C> {
    pub(super) fn configure(
        meta: &mut ConstraintSystem<F>,
        k: usize,
        m: Column<Advice>,
        x_p: Column<Advice>,
        y_p: Column<Advice>,
    ) -> (GeneratorInputs, Self) {
        let table_idx = meta.fixed_column();
        let table_x = meta.fixed_column();
        let table_y = meta.fixed_column();

        meta.lookup(
            &[m.into(), x_p.into(), y_p.into()],
            &[table_idx.into(), table_x.into(), table_y.into()],
        );

        (
            GeneratorInputs { m, x_p, y_p },
            GeneratorTable {
                k,
                table_idx,
                table_x,
                table_y,
                _marker_f: PhantomData,
                _marker_c: PhantomData,
            },
        )
    }

    // Generates P[0..2^k] as 2^k independent, verifiably random generators of the group.
    // Loads these generators into a lookup table along with their indices.
    // Uses SWU hash-to-curve.
    fn generate(&self) -> impl Iterator<Item = (F, F, F)> {
        let (init_x, init_y) = get_s_by_idx::<F, C>(0).to_affine().get_xy().unwrap();

        (1..=(1 << self.k)).scan((F::zero(), init_x, init_y), move |(idx, x, y), i| {
            // We computed this table row in the previous iteration.
            let res = (*idx, *x, *y);

            // i holds the zero-indexed row number for the next table row.
            *idx = F::from_u64(i as u64);

            let (new_x, new_y) = get_s_by_idx::<F, C>(i).to_affine().get_xy().unwrap();

            *x = new_x;
            *y = new_y;

            Some(res)
        })
    }

    pub(super) fn load(
        &self,
        layouter: &mut impl Layouter<SinsemillaChip<F, C>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "generator_table",
            |mut gate| {
                // We generate the row values lazily (we only need them during keygen).
                let mut rows = self.generate();

                for index in 0..(1 << self.k) {
                    let mut row = None;
                    gate.assign_fixed(
                        || "table_idx",
                        self.table_idx,
                        index,
                        || {
                            row = rows.next();
                            row.map(|(idx, _, _)| idx).ok_or(Error::SynthesisError)
                        },
                    )?;
                    gate.assign_fixed(
                        || "table_x",
                        self.table_x,
                        index,
                        || row.map(|(_, x, _)| x).ok_or(Error::SynthesisError),
                    )?;
                    gate.assign_fixed(
                        || "table_y",
                        self.table_y,
                        index,
                        || row.map(|(_, _, y)| y).ok_or(Error::SynthesisError),
                    )?;
                }
                Ok(())
            },
        )
    }
}

/// Get generator S by index
pub fn get_s_by_idx<F: FieldExt, C: CurveAffine<Base = F>>(idx: u64) -> C::Projective {
    let hash = C::Projective::hash_to_curve(S_DOMAIN_PREFIX);
    hash(&idx.to_le_bytes())
}
