use std::collections;

fn bubble_sort(seq: &mut Vec<i32>) -> Vec<i32> {
    let L: _ = seq.len();
    for _ in (0..L) {
        for n in (1..L) {
            if seq[n as usize] < seq[(n as i32 - 1) as usize] {
                ({
                    let (__tmp1, __tmp2) = (seq[n as usize], seq[(n as i32 - 1) as usize]);
                    seq[(n as i32 - 1) as usize] = __tmp1;
                    seq[n as usize] = __tmp2;
                });
            }
        }
    }
    return seq.to_vec();
}

fn main() {
    let mut unsorted: &mut Vec<i32> = &mut vec![14, 11, 19, 5, 16, 10, 19, 12, 5, 12];
    let expected: &Vec<i32> = &vec![5, 5, 10, 11, 12, 12, 14, 16, 19, 19];
    assert!(bubble_sort(unsorted) == *expected);
    println!("{}", "OK");
}
