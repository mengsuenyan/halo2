use halo2::{
    arithmetic::{Curve, FieldExt},
    model::ModelRecorder,
    pasta::{EqAffine, Fp, Fq},
    plonk::*,
    poly::{
        commitment::{Blind, Params},
        Rotation,
    },
    transcript::{DummyHashRead, DummyHashWrite},
};

use std::marker::PhantomData;

/// This represents an advice column at a certain row in the ConstraintSystem
#[derive(Copy, Clone, Debug)]
pub struct Variable(Column<Advice>, usize);

struct PLONKConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    sa: Column<Fixed>,
    sb: Column<Fixed>,
    sc: Column<Fixed>,
    sm: Column<Fixed>,
    sp: Column<Fixed>,

    perm: usize,
}

trait StandardCS<FF: FieldExt> {
    fn raw_multiply<F>(&mut self, f: F) -> Result<(Variable, Variable, Variable), Error>
    where
        F: FnOnce() -> Result<(FF, FF, FF), Error>;
    fn raw_add<F>(&mut self, f: F) -> Result<(Variable, Variable, Variable), Error>
    where
        F: FnOnce() -> Result<(FF, FF, FF), Error>;
    fn copy(&mut self, a: Variable, b: Variable) -> Result<(), Error>;
    fn public_input<F>(&mut self, f: F) -> Result<Variable, Error>
    where
        F: FnOnce() -> Result<FF, Error>;
}

struct MyCircuit<F: FieldExt> {
    a: Option<F>,
    k: u32,
}

struct StandardPLONK<'a, F: FieldExt, CS: Assignment<F> + 'a> {
    cs: &'a mut CS,
    config: PLONKConfig,
    current_gate: usize,
    _marker: PhantomData<F>,
}

impl<'a, FF: FieldExt, CS: Assignment<FF>> StandardPLONK<'a, FF, CS> {
    fn new(cs: &'a mut CS, config: PLONKConfig) -> Self {
        StandardPLONK {
            cs,
            config,
            current_gate: 0,
            _marker: PhantomData,
        }
    }
}

impl<'a, FF: FieldExt, CS: Assignment<FF>> StandardCS<FF> for StandardPLONK<'a, FF, CS> {
    fn raw_multiply<F>(&mut self, f: F) -> Result<(Variable, Variable, Variable), Error>
    where
        F: FnOnce() -> Result<(FF, FF, FF), Error>,
    {
        let index = self.current_gate;
        self.current_gate += 1;
        let mut value = None;
        self.cs.assign_advice(
            || "lhs",
            self.config.a,
            index,
            || {
                value = Some(f()?);
                Ok(value.ok_or(Error::SynthesisError)?.0)
            },
        )?;
        self.cs.assign_advice(
            || "rhs",
            self.config.b,
            index,
            || Ok(value.ok_or(Error::SynthesisError)?.1),
        )?;
        self.cs.assign_advice(
            || "out",
            self.config.c,
            index,
            || Ok(value.ok_or(Error::SynthesisError)?.2),
        )?;

        self.cs
            .assign_fixed(|| "a", self.config.sa, index, || Ok(FF::zero()))?;
        self.cs
            .assign_fixed(|| "b", self.config.sb, index, || Ok(FF::zero()))?;
        self.cs
            .assign_fixed(|| "c", self.config.sc, index, || Ok(FF::one()))?;
        self.cs
            .assign_fixed(|| "a * b", self.config.sm, index, || Ok(FF::one()))?;
        Ok((
            Variable(self.config.a, index),
            Variable(self.config.b, index),
            Variable(self.config.c, index),
        ))
    }
    fn raw_add<F>(&mut self, f: F) -> Result<(Variable, Variable, Variable), Error>
    where
        F: FnOnce() -> Result<(FF, FF, FF), Error>,
    {
        let index = self.current_gate;
        self.current_gate += 1;
        let mut value = None;
        self.cs.assign_advice(
            || "lhs",
            self.config.a,
            index,
            || {
                value = Some(f()?);
                Ok(value.ok_or(Error::SynthesisError)?.0)
            },
        )?;
        self.cs.assign_advice(
            || "rhs",
            self.config.b,
            index,
            || Ok(value.ok_or(Error::SynthesisError)?.1),
        )?;
        self.cs.assign_advice(
            || "out",
            self.config.c,
            index,
            || Ok(value.ok_or(Error::SynthesisError)?.2),
        )?;

        self.cs
            .assign_fixed(|| "a", self.config.sa, index, || Ok(FF::one()))?;
        self.cs
            .assign_fixed(|| "b", self.config.sb, index, || Ok(FF::one()))?;
        self.cs
            .assign_fixed(|| "c", self.config.sc, index, || Ok(FF::one()))?;
        self.cs
            .assign_fixed(|| "a * b", self.config.sm, index, || Ok(FF::zero()))?;
        Ok((
            Variable(self.config.a, index),
            Variable(self.config.b, index),
            Variable(self.config.c, index),
        ))
    }
    fn copy(&mut self, left: Variable, right: Variable) -> Result<(), Error> {
        let left_column = match left.0 {
            x if x == self.config.a => 0,
            x if x == self.config.b => 1,
            x if x == self.config.c => 2,
            _ => unreachable!(),
        };
        let right_column = match right.0 {
            x if x == self.config.a => 0,
            x if x == self.config.b => 1,
            x if x == self.config.c => 2,
            _ => unreachable!(),
        };

        self.cs
            .copy(self.config.perm, left_column, left.1, right_column, right.1)
    }
    fn public_input<F>(&mut self, f: F) -> Result<Variable, Error>
    where
        F: FnOnce() -> Result<FF, Error>,
    {
        let index = self.current_gate;
        self.current_gate += 1;
        self.cs
            .assign_advice(|| "value", self.config.a, index, || f())?;
        self.cs
            .assign_fixed(|| "public", self.config.sp, index, || Ok(FF::one()))?;

        Ok(Variable(self.config.a, index))
    }
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = PLONKConfig;

    fn configure(meta: &mut ConstraintSystem<F>) -> PLONKConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let p = meta.aux_column();

        let perm = meta.permutation(&[a, b, c]);

        let sm = meta.fixed_column();
        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();
        let sp = meta.fixed_column();

        meta.create_gate("Combined add-mult", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let sm = meta.query_fixed(sm, Rotation::cur());

            a.clone() * sa + b.clone() * sb + a * b * sm + (c * sc * (-F::one()))
        });

        meta.create_gate("Public input", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let p = meta.query_aux(p, Rotation::cur());
            let sp = meta.query_fixed(sp, Rotation::cur());

            sp * (a + p * (-F::one()))
        });

        PLONKConfig {
            a,
            b,
            c,
            sa,
            sb,
            sc,
            sm,
            sp,
            perm,
        }
    }

    fn synthesize(&self, cs: &mut impl Assignment<F>, config: PLONKConfig) -> Result<(), Error> {
        let mut cs = StandardPLONK::new(cs, config);

        let _ = cs.public_input(|| Ok(F::one() + F::one()))?;

        for _ in 0..((1 << (self.k - 1)) - 1) {
            let mut a_squared = None;
            let (a0, _, c0) = cs.raw_multiply(|| {
                a_squared = self.a.map(|a| a.square());
                Ok((
                    self.a.ok_or(Error::SynthesisError)?,
                    self.a.ok_or(Error::SynthesisError)?,
                    a_squared.ok_or(Error::SynthesisError)?,
                ))
            })?;
            let (a1, b1, _) = cs.raw_add(|| {
                let fin = a_squared.and_then(|a2| self.a.map(|a| a + a2));
                Ok((
                    self.a.ok_or(Error::SynthesisError)?,
                    a_squared.ok_or(Error::SynthesisError)?,
                    fin.ok_or(Error::SynthesisError)?,
                ))
            })?;
            cs.copy(a0, a1)?;
            cs.copy(b1, c0)?;
        }

        Ok(())
    }
}

fn main() {
    let recorder = Box::leak(Box::new(ModelRecorder::default()));
    metrics::set_recorder(recorder).unwrap();

    // TODO: Make dynamic.
    let k = 11;

    // Initialize the polynomial commitment parameters
    let params: Params<EqAffine> = Params::new(k);

    let empty_circuit: MyCircuit<Fp> = MyCircuit { a: None, k };

    // Initialize the proving key
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    println!("[Keygen] {}", recorder);
    recorder.clear();

    let mut pubinputs = pk.get_vk().get_domain().empty_lagrange();
    pubinputs[0] = Fp::one();
    pubinputs[0] += Fp::one();
    let pubinput = params
        .commit_lagrange(&pubinputs, Blind::default())
        .to_affine();
    recorder.clear();

    let circuit: MyCircuit<Fp> = MyCircuit {
        a: Some(Fp::rand()),
        k,
    };

    // Create a proof
    let mut transcript = DummyHashWrite::init(vec![], Fq::one());
    create_proof(&params, &pk, &circuit, &[pubinputs], &mut transcript)
        .expect("proof generation should not fail");
    let proof: Vec<u8> = transcript.finalize();

    println!("[Prover] {}", recorder);
    recorder.clear();

    let pubinput_slice = &[pubinput];
    let msm = params.empty_msm();
    let mut transcript = DummyHashRead::init(&proof[..], Fq::one());
    let guard = verify_proof(&params, pk.get_vk(), msm, pubinput_slice, &mut transcript).unwrap();
    let msm = guard.clone().use_challenges();
    assert!(msm.eval());

    println!("[Verifier] {}", recorder);
}
