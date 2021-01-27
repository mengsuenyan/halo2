use std::marker::PhantomData;

use super::{SinsemillaInstructions, Q_DOMAIN_PREFIX, Q_PERSONALIZATION};
use crate::{
    arithmetic::{Curve, CurveAffine, FieldExt},
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
    poly::Rotation,
};

mod generator_table;

use generator_table::*;

/// Configuration for the Sinsemilla chip
#[derive(Clone, Debug)]
pub struct SinsemillaConfig<F: FieldExt, C: CurveAffine<Base = F>> {
    /// Number of bits in a message word
    pub k: usize,
    /// Number of rounds in the Sinsemilla hash
    pub rounds: usize,
    ecc: Column<Fixed>,
    x_a: Column<Advice>,
    y_a: Column<Advice>,
    z: Column<Advice>,
    lambda1: Column<Advice>,
    lambda2: Column<Advice>,
    m: Column<Advice>,
    x_p: Column<Advice>,
    y_p: Column<Advice>,
    lookup_inputs: GeneratorInputs,
    lookup_table: GeneratorTable<F, C>,
}

/// A chip implementing SinsemillaInstructions
#[derive(Debug)]
pub struct SinsemillaChip<F: FieldExt, C: CurveAffine<Base = F>> {
    _marker_f: PhantomData<F>,
    _marker_c: PhantomData<C>,
}

impl<F: FieldExt, C: CurveAffine<Base = F>> SinsemillaChip<F, C> {
    /// Configures this chip for use in a circuit.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        k: usize,
        rounds: usize,
    ) -> SinsemillaConfig<F, C> {
        // Columns required by this chip:
        // Fixed column for ECC selector
        let ecc = meta.fixed_column();

        let x_a = meta.advice_column();
        let y_a = meta.advice_column();
        let z = meta.advice_column();
        let lambda1 = meta.advice_column();
        let lambda2 = meta.advice_column();

        // - Three advice columns to interact with the lookup table.
        let m = meta.advice_column();
        let x_p = meta.advice_column();
        let y_p = meta.advice_column();

        let (lookup_inputs, lookup_table) = GeneratorTable::configure(meta, k, m, x_p, y_p);

        // ECCLookup gate
        meta.create_gate("ECCLookup", |meta| {
            let ecc = meta.query_fixed(ecc, Rotation::cur());

            let x_a_cur = meta.query_advice(x_a, Rotation::cur());
            let y_a_cur = meta.query_advice(y_a, Rotation::cur());
            let x_a_next = meta.query_advice(x_a, Rotation::next());
            let y_a_next = meta.query_advice(y_a, Rotation::next());
            let lambda1 = meta.query_advice(lambda1, Rotation::cur());
            let lambda2 = meta.query_advice(lambda2, Rotation::cur());
            let x_p = meta.query_advice(x_p, Rotation::cur());
            let y_p = meta.query_advice(y_p, Rotation::cur());

            // λ_{1,i}⋅(x_{A,i} − x_{P,i}) − y_{A,i} + y_{P,i} = 0
            let expr1 = lambda1.clone() * (x_a_cur.clone() + x_p.clone() * (-F::one()))
                + y_a_cur.clone() * (-F::one())
                + y_p;

            // λ_{1,i} + λ_{2,i})⋅(x_{A,i} − (λ_{1,i}^2 − x_{A,i} − x_{P,i}))−2y_{A,i} = 0
            let expr2 = (lambda1.clone() + lambda2.clone())
                * (x_a_cur.clone()
                    + lambda1.clone() * lambda1.clone() * (-F::one())
                    + x_a_cur.clone()
                    + x_p.clone())
                + y_a_cur.clone() * (-F::one() - F::one());

            // λ_{2,i}^2 − x_{A,i+1} −(λ_{1,i}^2 − x_{A,i} − x_{P,i}) − x_{A,i} = 0
            let expr3 = lambda2.clone() * lambda2.clone()
                + x_a_next.clone() * (-F::one())
                + (lambda1.clone() * lambda1) * (-F::one())
                + x_p;

            // λ_{2,i}⋅(x_{A,i} − x_{A,i+1}) − y_{A,i} − y_{A,i+1} = 0
            let expr4 =
                lambda2 * (x_a_cur + x_a_next * (-F::one())) + (y_a_cur + y_a_next) * (-F::one());

            let z_cur = meta.query_advice(z, Rotation::cur());
            let z_next = meta.query_advice(z, Rotation::next());
            let m = meta.query_advice(m, Rotation::cur());

            // z_{i + 1} = (z_i * 2^k) + m_i
            let decompose_z = z_cur * F::from_u64((1 << k) as u64) + m + z_next * (-F::one());

            ecc * (expr1 + expr2 + expr3 + expr4 + decompose_z)
        });

        SinsemillaConfig::<F, C> {
            k,
            rounds,
            ecc,
            x_a,
            y_a,
            z,
            lambda1,
            lambda2,
            m,
            x_p,
            y_p,
            lookup_inputs,
            lookup_table,
        }
    }
}

impl<F: FieldExt, C: CurveAffine<Base = F>> Chip for SinsemillaChip<F, C> {
    type Config = SinsemillaConfig<F, C>;
    type Field = F;

    fn load(layouter: &mut impl Layouter<Self>) -> Result<(), Error> {
        let table = layouter.config().lookup_table.clone();
        table.load(layouter)
    }
}

impl<F: FieldExt, C: CurveAffine<Base = F>> SinsemillaInstructions<F, C> for SinsemillaChip<F, C> {
    type Message = Vec<bool>;
    type PaddedMessage = Vec<bool>;
    type HashOutput = C;

    fn q() -> (F, F) {
        let hash = C::Projective::hash_to_curve(Q_DOMAIN_PREFIX);
        let q = hash(&Q_PERSONALIZATION).to_affine();
        q.get_xy().unwrap()
    }

    /// Pads the given message to `kn` bits.
    fn pad(
        layouter: &mut impl Layouter<Self>,
        message: Self::Message,
    ) -> Result<Self::PaddedMessage, Error> {
        let k = layouter.config().k;
        let rounds = layouter.config().rounds;
        let padding = vec![false; k * rounds - message.len()];
        let mut message = message;
        message.extend_from_slice(&padding);

        Ok(message.to_vec())
    }

    /// Hashes the given message.
    ///
    /// TODO: Since the output is always curve point, maybe this should return
    /// `<Self as EccInstructions>::Point` instead of an associated type.
    fn hash(
        layouter: &mut impl Layouter<Self>,
        message: Self::PaddedMessage,
    ) -> Result<Self::HashOutput, Error> {
        let config = layouter.config().clone();

        // Parse message into `n` `k`-bit words
        let words: Vec<u64> = (0..config.rounds)
            .map(|i| {
                let mut word = 0u64;
                for j in 0..config.k {
                    word += (message[i * config.k + j] as u64) << j;
                }
                word
            })
            .collect();

        // Get (x_p, y_p) for each word. We precompute this here so that we can use `batch_to_affine()`.
        let generators_projective: Vec<_> = words
            .iter()
            .map(|word| get_s_by_idx::<F, C>(*word))
            .collect();
        let mut generators = vec![C::zero(); generators_projective.len()];
        C::Projective::batch_to_affine(&generators_projective, &mut generators);
        let generators: Vec<(F, F)> = generators.iter().map(|gen| gen.get_xy().unwrap()).collect();

        // Initialize `z_0` = 0;
        let mut z = 0u64;

        // Initialize `(x_a, y_a)` to be `(x_q, y_q)`
        let (mut x_a, mut y_a) = Self::q();

        layouter.assign_region(
            || "Assign message",
            |mut region| {
                // Assign initialized values
                region.assign_advice(|| "z_0", config.z, 0, || Ok(F::from_u64(z)))?;
                region.assign_advice(|| "x_q", config.x_a, 0, || Ok(x_a))?;
                region.assign_advice(|| "y_q", config.y_a, 0, || Ok(y_a))?;

                for row in 0..config.rounds {
                    let word = words[row];
                    let gen = generators[row];

                    // Activate `ECCLookup` custom gate
                    region.assign_fixed(|| "ECC lookup", config.ecc, row, || Ok(F::one()))?;

                    // Assign message word
                    region.assign_advice(
                        || "message word",
                        config.m,
                        row,
                        || Ok(F::from_u64(word)),
                    )?;

                    // Assign `x_p, y_p`
                    region.assign_advice(|| "x_p", config.x_p, row, || Ok(gen.0))?;
                    region.assign_advice(|| "y_p", config.y_p, row, || Ok(gen.1))?;

                    // Compute and assign `z` for the next row
                    z = z * (1 << config.k) + word;
                    region.assign_advice(|| "z", config.z, row + 1, || Ok(F::from_u64(z)))?;

                    // Compute and assign `lambda1, lambda2`
                    let point_a = C::from_xy(x_a, y_a).unwrap();
                    let point_p = C::from_xy(gen.0, gen.1).unwrap();
                    let point_r = point_a + point_p;
                    let (x_r, _y_r) = point_r.to_affine().get_xy().unwrap();
                    let lambda1 = (y_a - gen.1) * (x_a - gen.0).invert().unwrap();
                    let lambda2 = F::from_u64(2) * y_a * (x_a - x_r).invert().unwrap() - lambda1;
                    region.assign_advice(|| "lambda1", config.lambda1, row, || Ok(lambda1))?;
                    region.assign_advice(|| "lambda2", config.lambda2, row, || Ok(lambda2))?;

                    // Compute and assign `x_a, y_a` for the next row
                    let x_a_new = lambda2 * lambda2 - x_a - x_r;
                    y_a = lambda2 * (x_a - x_a_new) - y_a;
                    x_a = x_a_new;
                    region.assign_advice(|| "x_a", config.x_a, row + 1, || Ok(x_a))?;
                    region.assign_advice(|| "y_a", config.y_a, row + 1, || Ok(y_a))?;
                }

                // Assign unused cells for the lookup argument
                for row in generators.len()..(1 << config.k) {
                    let word = words[0];
                    let point = generators[0];
                    region.assign_advice(|| "m", config.m, row, || Ok(F::from_u64(word)))?;
                    region.assign_advice(|| "x_p", config.x_p, row, || Ok(point.0))?;
                    region.assign_advice(|| "y_p", config.y_p, row, || Ok(point.1))?;
                }

                Ok(())
            },
        )?;

        Ok(C::from_xy(x_a, y_a).unwrap())
    }
}
