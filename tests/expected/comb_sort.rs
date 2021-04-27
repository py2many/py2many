use std::cmp;
use std::collections;

fn comb_sort(seq: &mut Vec<i32>) -> Vec<i32> {
    let mut gap: _ = seq.len();
    let mut swap: bool = true;
    while gap as i32 > 1 || swap {
        gap = cmp::max(1, (gap as f32 / 1.25).floor() as usize);
        swap = false;
        for i in (0..(seq.len() - gap)) {
            if seq[i as usize] > seq[(i + gap) as usize] {
                ({
                    let (__tmp1, __tmp2) = (seq[(i + gap) as usize], seq[i as usize]);
                    seq[i as usize] = __tmp1;
                    seq[(i + gap) as usize] = __tmp2;
                });
                swap = true;
            }
        }
    }
    return seq.to_vec();
}

fn main() {
    let mut unsorted: &mut Vec<i32> = &mut vec![14, 11, 19, 5, 16, 10, 19, 12, 5, 12];
    let expected: &Vec<i32> = &vec![5, 5, 10, 11, 12, 12, 14, 16, 19, 19];
    assert!(comb_sort(unsorted) == *expected);
    println!("{}", "OK");
}
