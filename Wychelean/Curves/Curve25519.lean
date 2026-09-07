import Wychelean.Curves.Curve25519.Basic
import Wychelean.Curves.Curve25519.TwistIndependence

/-!
# Curve25519
The specification proper lives in `Wychelean.Curves.Curve25519.Basic`, the primality certificates
it relies on in `Wychelean.Curves.Curve25519.Prime25519`, and the known-answer tests in
`Wychelean.Curves.Curve25519.Tests`. That the twisting parameter of `_scalarMul` does not affect its
output is proved in `Wychelean.Curves.Curve25519.TwistIndependence`, on top of the Weierstrass
scaling isomorphism of `Wychelean.Curves.Curve25519.WeierstrassScaling`.
-/
