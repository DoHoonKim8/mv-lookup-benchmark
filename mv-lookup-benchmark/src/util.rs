use halo2_proofs::halo2curves::group::ff::PrimeField;
use itertools::Itertools;

pub fn fe_to_bits_le<F: PrimeField>(fe: F) -> Vec<bool> {
    let repr = fe.to_repr();
    let bytes = repr.as_ref();
    bytes
        .iter()
        .flat_map(|byte| {
            let value = u8::from_le(*byte);
            let mut bits = vec![];
            for i in 0..8 {
                let mask = 1 << i;
                bits.push(value & mask > 0);
            }
            bits
        })
        .collect_vec()
}

pub fn usize_from_bits_le(bits: &[bool]) -> usize {
    bits.iter()
        .rev()
        .fold(0, |int, bit| (int << 1) + (*bit as usize))
}
