# ChaCha8Rand Known Answer Tests

* `c2sp_sample_output.txt` is the "Sample output" section of the [C2SP ChaCha8Rand specification](https://github.com/C2SP/C2SP/blob/fc7f312aff098ed080f3dd5a3da4fd820be17a2e/chacha8rand.md#sample-output): the first 2976 bytes (three iterations) of output for the seed `ABCDEFGHIJKLMNOPQRSTUVWXYZ123456`, 32 bytes per line. The same output appears, as little-endian `uint64`s, in Go's [`internal/chacha8rand` tests](https://github.com/golang/go/blob/c29444ef39a44ad56ddf7b3d2aa8a51df1163e04/src/internal/chacha8rand/rand_test.go).

Neither [CCTV](https://github.com/C2SP/CCTV) nor [Wycheproof](https://github.com/C2SP/wycheproof) has ChaCha8Rand vectors.
