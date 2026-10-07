use std::fs;
use serde::Deserialize;
use lwe_rust::kyber::kem::{keygen_internal, encaps_internal, decaps_internal, EncapsulationKey, DecapsulationKey, Ciphertext};
use lwe_rust::kyber::pke::{ML_KEM_512, ML_KEM_768, ML_KEM_1024};
use hex;

#[derive(Deserialize, Debug)]
struct PromptFile {
    #[serde(rename = "testGroups")]
    test_groups: Vec<PromptTestGroup>,
}

#[derive(Deserialize, Debug)]
struct PromptTestGroup {
    #[serde(rename = "tgId")]
    tg_id: u32,
    #[serde(rename = "parameterSet")]
    parameter_set: String,
    tests: Vec<PromptTest>,
}

#[derive(Deserialize, Debug)]
struct PromptTest {
    #[serde(rename = "tcId")]
    tc_id: u32,
    z: Option<String>,
    d: Option<String>,
    ek: Option<String>,
    m: Option<String>,
    c: Option<String>,
    dk: Option<String>,
}

#[derive(Deserialize, Debug)]
struct ExpectedFile {
    #[serde(rename = "testGroups")]
    test_groups: Vec<ExpectedTestGroup>,
}

#[derive(Deserialize, Debug)]
struct ExpectedTestGroup {
    #[serde(rename = "tgId")]
    tg_id: u32,
    tests: Vec<ExpectedTest>,
}

#[derive(Deserialize, Debug)]
struct ExpectedTest {
    #[serde(rename = "tcId")]
    tc_id: u32,
    ek: Option<String>,
    dk: Option<String>,
    c: Option<String>,
    k: Option<String>,
}



#[test]
fn test_acvp_keygen() {
    let prompt_data = fs::read_to_string("tests/kats/fips203/keygen_prompt.json").unwrap();
    let expected_data = fs::read_to_string("tests/kats/fips203/keygen_expected.json").unwrap();
    
    let prompt: PromptFile = serde_json::from_str(&prompt_data).unwrap();
    let expected: ExpectedFile = serde_json::from_str(&expected_data).unwrap();
    
    let mut total_tests = 0;

    for (ptg, etg) in prompt.test_groups.iter().zip(expected.test_groups.iter()) {
        assert_eq!(ptg.tg_id, etg.tg_id);
        let param_set = &ptg.parameter_set;
        
        for (pt, et) in ptg.tests.iter().zip(etg.tests.iter()) {
            assert_eq!(pt.tc_id, et.tc_id);
            
            let d_bytes = hex::decode(pt.d.as_ref().unwrap()).unwrap();
            let z_bytes = hex::decode(pt.z.as_ref().unwrap()).unwrap();
            
            let mut d_arr = [0u8; 32];
            d_arr.copy_from_slice(&d_bytes);
            let mut z_arr = [0u8; 32];
            z_arr.copy_from_slice(&z_bytes);
            
            let ek_exp = hex::decode(et.ek.as_ref().unwrap()).unwrap();
            let dk_exp = hex::decode(et.dk.as_ref().unwrap()).unwrap();
            
            if param_set == "ML-KEM-512" {
                let (ek, dk) = keygen_internal::<800, 1632>(&ML_KEM_512, &d_arr, &z_arr);
                assert_eq!(ek.0.as_slice(), ek_exp.as_slice(), "KeyGen ek mismatch at tcId {}", pt.tc_id);
                assert_eq!(dk.0.as_slice(), dk_exp.as_slice(), "KeyGen dk mismatch at tcId {}", pt.tc_id);
            } else if param_set == "ML-KEM-768" {
                let (ek, dk) = keygen_internal::<1184, 2400>(&ML_KEM_768, &d_arr, &z_arr);
                assert_eq!(ek.0.as_slice(), ek_exp.as_slice(), "KeyGen ek mismatch at tcId {}", pt.tc_id);
                assert_eq!(dk.0.as_slice(), dk_exp.as_slice(), "KeyGen dk mismatch at tcId {}", pt.tc_id);
            } else if param_set == "ML-KEM-1024" {
                let (ek, dk) = keygen_internal::<1568, 3168>(&ML_KEM_1024, &d_arr, &z_arr);
                assert_eq!(ek.0.as_slice(), ek_exp.as_slice(), "KeyGen ek mismatch at tcId {}", pt.tc_id);
                assert_eq!(dk.0.as_slice(), dk_exp.as_slice(), "KeyGen dk mismatch at tcId {}", pt.tc_id);
            }
            total_tests += 1;
        }
    }
    println!("Successfully passed {} ACVP KeyGen tests.", total_tests);
}

#[test]
fn test_acvp_encap_decap() {
    let prompt_data = fs::read_to_string("tests/kats/fips203/encapdecap_prompt.json").unwrap();
    let expected_data = fs::read_to_string("tests/kats/fips203/encapdecap_expected.json").unwrap();
    
    let prompt: PromptFile = serde_json::from_str(&prompt_data).unwrap();
    let expected: ExpectedFile = serde_json::from_str(&expected_data).unwrap();
    
    let mut total_encaps = 0;
    let mut total_decaps = 0;

    for (ptg, etg) in prompt.test_groups.iter().zip(expected.test_groups.iter()) {
        assert_eq!(ptg.tg_id, etg.tg_id);
        let param_set = &ptg.parameter_set;
        
        for (pt, et) in ptg.tests.iter().zip(etg.tests.iter()) {
            assert_eq!(pt.tc_id, et.tc_id);
            
            if let (Some(ek_hex), Some(m_hex)) = (&pt.ek, &pt.m) {
                // Encapsulation
                let ek_bytes = hex::decode(ek_hex).unwrap();
                let m = hex::decode(m_hex).unwrap();
                let mut m_arr = [0u8; 32];
                m_arr.copy_from_slice(&m);
                
                let k_exp = hex::decode(et.k.as_ref().unwrap()).unwrap();
                let c_exp = hex::decode(et.c.as_ref().unwrap()).unwrap();
                
                if param_set == "ML-KEM-512" {
                    let mut ek_array = [0u8; 800];
                    ek_array.copy_from_slice(&ek_bytes);
                    let ek = EncapsulationKey(ek_array);
                    let (k, c) = encaps_internal::<800, 768>(&ML_KEM_512, &ek, &m_arr);
                    assert_eq!(k.0.as_slice(), k_exp.as_slice(), "Encaps k mismatch at tcId {}", pt.tc_id);
                    assert_eq!(c.0.as_slice(), c_exp.as_slice(), "Encaps c mismatch at tcId {}", pt.tc_id);
                } else if param_set == "ML-KEM-768" {
                    let mut ek_array = [0u8; 1184];
                    ek_array.copy_from_slice(&ek_bytes);
                    let ek = EncapsulationKey(ek_array);
                    let (k, c) = encaps_internal::<1184, 1088>(&ML_KEM_768, &ek, &m_arr);
                    assert_eq!(k.0.as_slice(), k_exp.as_slice(), "Encaps k mismatch at tcId {}", pt.tc_id);
                    assert_eq!(c.0.as_slice(), c_exp.as_slice(), "Encaps c mismatch at tcId {}", pt.tc_id);
                } else if param_set == "ML-KEM-1024" {
                    let mut ek_array = [0u8; 1568];
                    ek_array.copy_from_slice(&ek_bytes);
                    let ek = EncapsulationKey(ek_array);
                    let (k, c) = encaps_internal::<1568, 1568>(&ML_KEM_1024, &ek, &m_arr);
                    assert_eq!(k.0.as_slice(), k_exp.as_slice(), "Encaps k mismatch at tcId {}", pt.tc_id);
                    assert_eq!(c.0.as_slice(), c_exp.as_slice(), "Encaps c mismatch at tcId {}", pt.tc_id);
                }
                
                total_encaps += 1;
            } else if let (Some(dk_hex), Some(c_hex)) = (&pt.dk, &pt.c) {
                // Decapsulation
                let dk_bytes = hex::decode(dk_hex).unwrap();
                let c_bytes = hex::decode(c_hex).unwrap();
                let k_exp = hex::decode(et.k.as_ref().unwrap()).unwrap();
                
                if param_set == "ML-KEM-512" {
                    let mut dk_array = [0u8; 1632];
                    dk_array.copy_from_slice(&dk_bytes);
                    let mut c_array = [0u8; 768];
                    c_array.copy_from_slice(&c_bytes);
                    let k = decaps_internal::<800, 1632, 768>(&ML_KEM_512, &DecapsulationKey(dk_array), &Ciphertext(c_array));
                    assert_eq!(k.0.as_slice(), k_exp.as_slice(), "Decaps k mismatch at tcId {}", pt.tc_id);
                } else if param_set == "ML-KEM-768" {
                    let mut dk_array = [0u8; 2400];
                    dk_array.copy_from_slice(&dk_bytes);
                    let mut c_array = [0u8; 1088];
                    c_array.copy_from_slice(&c_bytes);
                    let k = decaps_internal::<1184, 2400, 1088>(&ML_KEM_768, &DecapsulationKey(dk_array), &Ciphertext(c_array));
                    assert_eq!(k.0.as_slice(), k_exp.as_slice(), "Decaps k mismatch at tcId {}", pt.tc_id);
                } else if param_set == "ML-KEM-1024" {
                    let mut dk_array = [0u8; 3168];
                    dk_array.copy_from_slice(&dk_bytes);
                    let mut c_array = [0u8; 1568];
                    c_array.copy_from_slice(&c_bytes);
                    let k = decaps_internal::<1568, 3168, 1568>(&ML_KEM_1024, &DecapsulationKey(dk_array), &Ciphertext(c_array));
                    assert_eq!(k.0.as_slice(), k_exp.as_slice(), "Decaps k mismatch at tcId {}", pt.tc_id);
                }
                
                total_decaps += 1;
            }
        }
    }
    println!("Successfully passed {} ACVP Encaps tests and {} ACVP Decaps tests.", total_encaps, total_decaps);
}
