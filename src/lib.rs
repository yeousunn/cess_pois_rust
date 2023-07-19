pub mod acc;
pub mod expanders;
pub mod pois;
pub mod tree;
pub mod util;

#[cfg(test)]
mod tests {
    use crate::util::parse_key;
    use crate::{
        acc::RsaKey,
        pois::{
            prove::{AccProof, Commit, CommitProof, DeletionProof, SpaceProof},
            verify::Verifier,
        },
    };

    #[test]
    fn test_receive_commits() {
        let (mut verifier, key, id) = init_fields();

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), &key.g.to_bytes_be(), 0, 0);

        let mut commits = init_commit();

        // Commits received
        assert_eq!(verifier.receive_commits(id, &mut commits), true);
    }

    #[test]
    fn test_commit_challenges() {
        let (mut verifier, key, id) = init_fields();

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), &key.g.to_bytes_be(), 0, 0);

        let mut commits = init_commit();

        if !verifier.receive_commits(id, &mut commits) {
            assert!(false);
        }

        let chals = verifier.commit_challenges(id, 0, 4);

        if let Ok(_) = chals {
            assert!(true);
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_space_challenges() {
        let (mut verifier, key, id) = init_fields();

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), &key.g.to_bytes_be(), 0, 0);

        let chals = verifier.space_challenges(22);

        if let Ok(_) = chals {
            assert!(true);
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_verify_commit_proofs() {
        let (mut verifier, key, id) = init_fields();

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), &key.g.to_bytes_be(), 0, 0);

        let mut commits = init_commit();

        if !verifier.receive_commits(id, &mut commits) {
            assert!(false);
        }

        // To test replace this with vector of CommitProof with data
        let proofs: Vec<Vec<CommitProof>> = Vec::new();

        if let Ok(chals) = verifier.commit_challenges(id, 0, 4) {
            if let Err(err) = verifier.verify_commit_proofs(id, chals, proofs) {
                debug_assert!(false, "{}", format!("{:?}", err));
            }
        }
    }

    #[test]
    fn test_verify_acc() {
        let (mut verifier, key, id) = init_fields();

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), &key.g.to_bytes_be(), 0, 0);

        let mut commits = init_commit();

        if !verifier.receive_commits(id, &mut commits) {
            assert!(false);
        }

        // To test replace this with AccProof object
        let proofs: AccProof = AccProof {
            ..Default::default()
        };

        if let Ok(chals) = verifier.commit_challenges(id, 0, 4) {
            if let Err(err) = verifier.verify_acc(id, chals, proofs) {
                eprintln!("{}", err);
                assert!(false)
            }
        }
    }

    #[test]
    fn test_verify_space() {
        let (mut verifier, key, id) = init_fields();

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), &key.g.to_bytes_be(), 0, 0);

        if let Ok(p_node) = verifier.get_node(id) {
            if let Ok(space_chals) = verifier.space_challenges(22) {
                let mut space_proof = SpaceProof {
                    ..Default::default()
                };
                if let Err(err) = verifier.verify_space(p_node, space_chals, &mut space_proof) {
                    eprintln!("{}", err);
                    assert!(false)
                }
            }
        }
    }

    #[test]
    fn test_verify_deletion() {
        let (mut verifier, key, id) = init_fields();

        // Register prover node with the verifier
        verifier.register_prover_node(id, key.clone(), &key.g.to_bytes_be(), 0, 0);

        let mut deletion_proof = DeletionProof {
            ..Default::default()
        };
        if let Err(err) = verifier.verify_deletion(id, &mut deletion_proof) {
            eprintln!("{}", err);
            assert!(false)
        }
    }

    fn init_fields() -> (Verifier, RsaKey, &'static [u8]) {
        let verifier = Verifier::new(1, 512, 32);
        // let key = acc::rsa_keygen(2048);
        let key = parse_key("./key").unwrap();
        let id = b"test miner id";

        (verifier, key, id)
    }

    fn init_commit() -> Vec<Commit> {
        vec![
            Commit {
                file_index: 1,
                roots: vec![
                    vec![
                        129, 208, 232, 95, 249, 86, 213, 83, 196, 183, 29, 167, 7, 68, 69, 253,
                        202, 194, 114, 209, 12, 234, 236, 200, 234, 136, 131, 42, 252, 192, 106,
                        183, 1, 225, 160, 241, 63, 63, 237, 90, 209, 169, 157, 51, 1, 30, 97, 215,
                        220, 120, 179, 37, 221, 146, 223, 90, 158, 226, 11, 98, 180, 95, 74, 118,
                    ],
                    vec![
                        157, 6, 210, 195, 248, 145, 203, 9, 148, 45, 218, 23, 43, 170, 214, 42, 81,
                        70, 47, 161, 197, 124, 111, 169, 120, 23, 193, 16, 2, 154, 214, 95, 166,
                        211, 80, 83, 60, 195, 205, 1, 158, 126, 11, 165, 80, 126, 25, 172, 216,
                        124, 227, 27, 52, 161, 100, 57, 200, 5, 187, 206, 58, 233, 122, 153,
                    ],
                    vec![
                        207, 152, 225, 28, 141, 61, 43, 90, 16, 214, 39, 205, 43, 214, 206, 87,
                        192, 92, 210, 120, 43, 239, 115, 26, 123, 205, 180, 12, 43, 80, 236, 183,
                        6, 173, 120, 87, 249, 28, 125, 180, 5, 116, 132, 126, 231, 205, 181, 220,
                        98, 108, 173, 3, 25, 163, 102, 39, 221, 78, 121, 19, 4, 145, 229, 202,
                    ],
                ],
            },
            Commit {
                file_index: 2,
                roots: vec![
                    vec![
                        105, 194, 234, 123, 181, 216, 213, 65, 169, 242, 197, 188, 176, 54, 62,
                        155, 117, 249, 61, 34, 137, 31, 10, 141, 232, 236, 188, 127, 133, 106, 50,
                        136, 127, 143, 186, 246, 209, 76, 103, 92, 42, 40, 115, 166, 227, 161, 33,
                        233, 175, 25, 72, 25, 232, 1, 219, 82, 21, 117, 143, 208, 252, 196, 225,
                        238,
                    ],
                    vec![
                        136, 182, 14, 188, 56, 232, 174, 221, 83, 60, 134, 111, 147, 35, 128, 172,
                        2, 51, 156, 120, 132, 152, 46, 69, 235, 112, 133, 122, 200, 46, 239, 173,
                        53, 188, 148, 9, 45, 128, 1, 133, 160, 175, 105, 29, 4, 34, 75, 59, 81, 41,
                        100, 90, 69, 241, 31, 174, 96, 103, 138, 41, 120, 222, 227, 242,
                    ],
                    vec![
                        204, 129, 223, 155, 138, 218, 139, 118, 30, 100, 113, 96, 75, 161, 67, 233,
                        223, 30, 205, 155, 171, 164, 32, 161, 16, 22, 148, 215, 184, 252, 228, 5,
                        86, 11, 113, 179, 106, 240, 183, 89, 125, 217, 10, 185, 33, 211, 230, 177,
                        159, 69, 69, 156, 48, 53, 112, 190, 133, 38, 227, 98, 237, 90, 209, 185,
                    ],
                ],
            },
            Commit {
                file_index: 3,
                roots: vec![
                    vec![
                        251, 152, 192, 124, 183, 126, 22, 198, 131, 59, 208, 40, 164, 228, 231, 99,
                        112, 26, 234, 125, 203, 172, 190, 150, 185, 202, 217, 198, 186, 153, 72,
                        25, 59, 101, 254, 180, 180, 232, 105, 217, 144, 187, 236, 248, 211, 175,
                        180, 246, 130, 160, 168, 116, 105, 44, 115, 118, 93, 254, 193, 146, 165,
                        75, 56, 123,
                    ],
                    vec![
                        62, 35, 50, 182, 151, 147, 96, 102, 173, 210, 115, 32, 65, 69, 212, 130,
                        140, 77, 172, 92, 243, 89, 169, 101, 68, 16, 247, 69, 92, 202, 121, 139,
                        197, 53, 76, 106, 152, 48, 99, 122, 189, 146, 157, 14, 128, 4, 146, 7, 97,
                        55, 157, 57, 177, 5, 77, 213, 38, 122, 174, 166, 124, 63, 104, 1,
                    ],
                    vec![
                        107, 227, 158, 56, 129, 159, 81, 61, 181, 91, 239, 161, 166, 155, 110, 33,
                        4, 32, 24, 253, 168, 157, 164, 153, 57, 203, 136, 197, 239, 72, 247, 47,
                        141, 7, 161, 181, 37, 62, 3, 248, 187, 143, 7, 77, 237, 225, 49, 7, 146,
                        80, 237, 188, 152, 177, 161, 6, 116, 111, 120, 171, 221, 171, 63, 42,
                    ],
                ],
            },
            Commit {
                file_index: 4,
                roots: vec![
                    vec![
                        231, 160, 10, 151, 1, 121, 163, 135, 116, 207, 59, 124, 55, 31, 112, 54,
                        136, 114, 51, 75, 86, 103, 132, 173, 38, 11, 207, 98, 176, 63, 108, 251,
                        130, 246, 221, 74, 118, 119, 65, 123, 110, 175, 223, 44, 24, 24, 155, 255,
                        241, 210, 144, 225, 94, 124, 22, 8, 224, 13, 113, 31, 191, 44, 31, 254,
                    ],
                    vec![
                        36, 214, 131, 14, 174, 60, 168, 239, 13, 45, 194, 136, 212, 28, 119, 44,
                        105, 171, 83, 140, 116, 121, 125, 44, 99, 118, 124, 65, 179, 139, 212, 25,
                        86, 155, 41, 92, 39, 240, 75, 221, 118, 26, 216, 82, 83, 231, 86, 25, 181,
                        239, 80, 129, 167, 30, 51, 75, 58, 23, 155, 237, 116, 43, 138, 214,
                    ],
                    vec![
                        52, 149, 50, 251, 125, 102, 147, 71, 37, 245, 21, 80, 173, 30, 2, 101, 18,
                        106, 139, 106, 251, 27, 250, 121, 187, 135, 22, 131, 114, 213, 12, 206,
                        228, 232, 79, 246, 222, 74, 119, 49, 125, 21, 9, 95, 143, 189, 239, 80,
                        193, 157, 218, 93, 233, 230, 227, 236, 2, 114, 84, 200, 99, 92, 167, 177,
                    ],
                ],
            },
        ]
    }
}
