# ML-KEM Test Vectors

* `symcrypt_acvp.rsp` holds the three NIST ACVP vectors (one per parameter set) embedded in the
  test file of the [SymCrypt Lean specification](https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/SpecTests/MLKEM/TestVectors.lean)
  (MIT; see `Wychelean/Hashes/SHA3/LICENSE.SymCrypt`), which attributes them to SymCrypt's
  `unittest/kat_kem.dat`, derived from NIST ACVP ML-KEM-keyGen-FIPS203 and
  ML-KEM-encapDecap-FIPS203. Hex is lowercased; values are otherwise unchanged.
* `mlkem_*.json` come unchanged from the [Wycheproof](https://github.com/C2SP/wycheproof) project
  at commit `3fa63dd0344abb611f1fb1d77e119938603ea230` (Apache 2.0; see `LICENSE.Wycheproof`):
  - [`mlkem_1024_encaps_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_1024_encaps_test.json "sha256sum: da41e8daf57e40a6b334a722e3f56067817352f5583fdb2434da1a2cd611358e")
  - [`mlkem_1024_keygen_seed_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_1024_keygen_seed_test.json "sha256sum: cd9241bf5d65a78e005866ea2c660615c17f50caa9afc2b96fd1573cc65617b5")
  - [`mlkem_1024_semi_expanded_decaps_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_1024_semi_expanded_decaps_test.json "sha256sum: a4a7c88152df3d8d4b3f33aad584167dfaff67195cfde08aac4b981030b4d05c")
  - [`mlkem_1024_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_1024_test.json "sha256sum: 17c5b764d78c05522f1980fcb41d82add573f11de5d13004ae0b83bf46d9c43a")
  - [`mlkem_512_encaps_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_512_encaps_test.json "sha256sum: 85a69664f2e8243f5085f01fb22f9635b100b16a8935cf2b2ac94c127511a20c")
  - [`mlkem_512_keygen_seed_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_512_keygen_seed_test.json "sha256sum: 877ae6f5550d0e802086e5812bdbd23c16afa31cd3bff9669cd9661d3fbf2d85")
  - [`mlkem_512_semi_expanded_decaps_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_512_semi_expanded_decaps_test.json "sha256sum: bb90c7997dc3695e52882608b7c79675a012c031dd50dc08e76c4775a762ad14")
  - [`mlkem_512_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_512_test.json "sha256sum: 18bc5455d5bf8226b3ab1d1deb51f3ed7c44b3d90039eb25416d40fa77e76f20")
  - [`mlkem_768_encaps_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_768_encaps_test.json "sha256sum: 9d4381f94c40853bba430245b94968b7390d9175aacd9f1ae4e250a71c78b713")
  - [`mlkem_768_keygen_seed_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_768_keygen_seed_test.json "sha256sum: fde5abe284396f4cb3c4610b90d680f0b57782e94c3365c97aee59e24881ebe4")
  - [`mlkem_768_semi_expanded_decaps_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_768_semi_expanded_decaps_test.json "sha256sum: e4438ab7d4dd7b6ace7165e45aeed4403082f981f86300c8369f69d3d071060a")
  - [`mlkem_768_test.json`](https://github.com/C2SP/wycheproof/blob/3fa63dd0344abb611f1fb1d77e119938603ea230/testvectors_v1/mlkem_768_test.json "sha256sum: c59c067ae794c343df575dd90f6f7458f51881b11a22d6e9d8677c8d9ee21e90")
