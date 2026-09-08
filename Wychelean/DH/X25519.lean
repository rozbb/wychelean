import Wychelean.DH.X25519.Basic
import Wychelean.DH.X25519.TwistIndependence

/-!
# X25519

The specification proper lives in `Wychelean.DH.X25519.Basic`, the primality certificates
it relies on in `Wychelean.DH.X25519.Prime25519`, and the known-answer tests in
`Wychelean.DH.X25519.Tests`. That the twisting parameter of `scalarMulGeneric` does not
affect its output is proved in `Wychelean.DH.X25519.TwistIndependence`, on top of the
Weierstrass scaling isomorphism of `Wychelean.DH.X25519.WeierstrassScaling`.
-/
