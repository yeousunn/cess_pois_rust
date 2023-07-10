pub fn copy_data(target: &mut Vec<u8>, src: &[&[u8]]) {
    let mut count = 0;
    let lens = target.len();

    for d in src {
        let l = d.len();
        if l == 0 || l + count > lens {
            continue;
        }
        target[count..count + l].copy_from_slice(d);
        count += l;
    }
}
