use sha3::{self, get_vec_of_bits, hex_of_vec_of_bits};

fn main() -> std::io::Result<()> {
    let mut iter = std::env::args();
    let _exe = iter.next();
    // println!("args");
    // for arg in std::env::args() {
    //     println!("{}", arg);
    // }
    // println!("args done");
    loop {
        let Some(op) = iter.next() else {break};
        let msg = iter.next().unwrap_or("".to_string());
        let bs: Vec<bool> = get_vec_of_bits(&msg);
        let output = match op.as_str() {
            "SHA3_224" => {
                sha3::simple::sha3_224(&bs).to_vec()
            }
            "SHA3_256" => {
                sha3::simple::sha3_256(&bs).to_vec()
            }
            "SHA3_384" => {
                sha3::simple::sha3_384(&bs).to_vec()
            }
            "SHA3_512" => {
                sha3::simple::sha3_512(&bs).to_vec()
            }
            "SHAKE128" => {
                let Some(Ok(d)) = iter.next().map(|x| usize::from_str_radix(&x, 10)) else {break};
                let mut output = Vec::new(); for _ in 0..d { output.push(false); }
                sha3::simple::shake128(&bs, &mut output);
                output.to_vec()
            }
            "SHAKE256" => {
                let Some(Ok(d)) = iter.next().map(|x| usize::from_str_radix(&x, 10)) else {break};
                let mut output = Vec::new(); for _ in 0..d { output.push(false); }
                sha3::simple::shake256(&bs, &mut output);
                output.to_vec()
            }
            _ => break
        };
        println!("{}", hex_of_vec_of_bits(&output));
    }
    return Ok(())
}
