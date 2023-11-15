mod util;

use std::time::Instant;

use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::FieldExt;
use halo2_proofs::halo2curves::bn256::{Fr, Bn256};
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector, keygen_vk, keygen_pk,
    create_proof, verify_proof, TableColumn,
};
use halo2_proofs::poly::Rotation;
use halo2_proofs::poly::commitment::ParamsProver;
use halo2_proofs::poly::kzg::commitment::ParamsKZG;
use halo2_proofs::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use halo2_proofs::transcript::{Blake2bWrite, TranscriptWriterBuffer, Blake2bRead, TranscriptReadBuffer};
use itertools::Itertools;
use rand::{RngCore, SeedableRng, CryptoRng};
use rand::rngs::{OsRng, StdRng};

use crate::util::{fe_to_bits_le, usize_from_bits_le};

#[derive(Clone, Debug)]
pub struct RangeCircuitConfig {
    pub(crate) a1: Column<Advice>,
    pub(crate) a2: Column<Advice>,
    pub(crate) a3: Column<Advice>,
    pub(crate) a4: Column<Advice>,
    pub(crate) a5: Column<Advice>,
    pub(crate) a6: Column<Advice>,
    pub(crate) a7: Column<Advice>,
    pub(crate) a8: Column<Advice>,
    pub(crate) w: Column<Advice>,

    pub(crate) t: TableColumn,
    pub(crate) s_gate: Selector,
    pub(crate) s_lookup: Selector,
}

pub struct RangeCircuit {
    inputs: Vec<Fr>,
}

impl Circuit<Fr> for RangeCircuit {
    type Config = RangeCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { inputs: vec![] }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a1 = meta.advice_column();
        let a2 = meta.advice_column();
        let a3 = meta.advice_column();
        let a4 = meta.advice_column();
        let a5 = meta.advice_column();
        let a6 = meta.advice_column();
        let a7 = meta.advice_column();
        let a8 = meta.advice_column();
        let w = meta.advice_column();
        let s_gate = meta.selector();

        let t = meta.lookup_table_column();
        let s_lookup = meta.complex_selector();

        meta.create_gate("composition", |meta| {
            let a1 = meta.query_advice(a1, Rotation::cur());
            let a2 = meta.query_advice(a2, Rotation::cur());
            let a3 = meta.query_advice(a3, Rotation::cur());
            let a4 = meta.query_advice(a4, Rotation::cur());
            let a5 = meta.query_advice(a5, Rotation::cur());
            let a6 = meta.query_advice(a6, Rotation::cur());
            let a7 = meta.query_advice(a7, Rotation::cur());
            let a8 = meta.query_advice(a8, Rotation::cur());

            let w = meta.query_advice(w, Rotation::cur());
            let s_gate = meta.query_selector(s_gate);

            let composed = [a2, a3, a4, a5, a6, a7, a8]
                .into_iter()
                .enumerate()
                .fold(a1, |acc, (i, expr)| {
                    acc + expr * Expression::Constant(Fr::from(1 << (16 * (i + 1))))
                });
            vec![s_gate * (composed - w)]
        });

        for col in [a1, a2, a3, a4, a5, a6, a7, a8] {
            meta.lookup("", |meta| {
                let selector = meta.query_selector(s_lookup);
                let value = meta.query_advice(col, Rotation::cur());
                vec![(selector * value, t)]
            });
        }

        RangeCircuitConfig {
            a1,
            a2,
            a3,
            a4,
            a5,
            a6,
            a7,
            a8,
            w,
            s_gate,
            t,
            s_lookup,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |mut region| {
                self.inputs.iter().enumerate().for_each(|(i, input)| {
                    let input_bits = &fe_to_bits_le(input.clone())[..128];
                    assert_eq!(
                        Fr::from_u128(usize_from_bits_le(input_bits) as u128),
                        *input
                    );
                    config.s_gate.enable(&mut region, i).unwrap();
                    config.s_lookup.enable(&mut region, i).unwrap();
                    region
                        .assign_advice(|| "", config.w, i, || Value::known(*input))
                        .unwrap();
                    [
                        config.a1, config.a2, config.a3, config.a4, config.a5, config.a6,
                        config.a7, config.a8,
                    ]
                    .iter()
                    .zip(input_bits.chunks(16))
                    .map(|(col, limb)| {
                        region.assign_advice(
                            || "",
                            *col,
                            i,
                            || Value::known(Fr::from(usize_from_bits_le(limb) as u64)),
                        )
                    })
                    .collect::<Result<Vec<_>, Error>>()
                    .unwrap();
                });

                Ok(())
            },
        )?;

        // load table
        layouter.assign_table(
            || "",
            |mut table| {
                let mut offset = 0;
                let table_values: Vec<Fr> = (0..1 << 16).map(|e| Fr::from(e as u64)).collect();
                for value in table_values.iter() {
                    table.assign_cell(|| "", config.t, offset, || Value::known(*value))?;
                    offset += 1;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

fn std_rng() -> impl RngCore + CryptoRng {
    StdRng::from_seed(Default::default())
}

fn main() {
    let k = 17;
    let mut rng = std_rng();
    let inputs = vec![(); 1 << (k-1)]
        .iter()
        .map(|_| {
            let value = rng.next_u64() as usize;
            Fr::from_u128(value.pow(2) as u128)
        })
        .collect_vec();
    let circuit = RangeCircuit { inputs };

    MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

    let param = ParamsKZG::<Bn256>::new(k);
    let vk = keygen_vk(&param, &circuit).unwrap();
    let pk = keygen_pk(&param, vk, &circuit).unwrap();

    let create_proof = |c, d, e, mut f: Blake2bWrite<_, _, _>| {
        create_proof::<_, ProverGWC<_>, _, _, _, _>(
            &param,
            &pk,
            c,
            d,
            e,
            &mut f)
        .unwrap();
        f.finalize()
    };

    let verify_proof =
        |c, d, e| verify_proof::<_, VerifierGWC<_>, _, _, _>(&param, pk.get_vk(), c, d, e);

    let proof = {
        let transcript = Blake2bWrite::init(Vec::new());
        let start = Instant::now();
        let proof = create_proof(&[circuit], &[&[]], std_rng(), transcript);
        println!("proving time : {}", start.elapsed().as_millis());
        proof
    };

    let accept = {
        let mut transcript = Blake2bRead::init(proof.as_slice());
        let strategy = SingleStrategy::new(&param);
        verify_proof(strategy, &[&[]], &mut transcript).is_ok()
    };
    assert!(accept)
}
