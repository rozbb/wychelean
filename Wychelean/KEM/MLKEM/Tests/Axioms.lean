import Wychelean.KEM.MLKEM.Properties

/-! The public arithmetic bridges must depend only on standard Lean axioms. -/

/-- info: 'Wychelean.KEM.MLKEM.Tq.abstractRingEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.Tq.abstractRingEquiv

/-- info: 'Wychelean.KEM.MLKEM.nttEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.nttEquiv

/-- info: 'Wychelean.KEM.MLKEM.toAbstract_ntt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.toAbstract_ntt

/-- info: 'Wychelean.KEM.MLKEM.nttInv_eq_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.nttInv_eq_abstract

/-- info: 'Wychelean.KEM.MLKEM.Tq.toAbstract_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.Tq.toAbstract_mul

/-- info: 'Wychelean.KEM.MLKEM.nttInv_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.nttInv_mul

/-- info: 'Wychelean.KEM.MLKEM.ntt_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_eq_iff

/-- info: 'Wychelean.KEM.MLKEM.ntt_eq_iff_toR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_eq_iff_toR

/-- info: 'Wychelean.KEM.MLKEM.NTT.inverseStage_splitInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.NTT.inverseStage_splitInv

/-- info: 'Wychelean.KEM.MLKEM.nttInv_ntt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.nttInv_ntt

/-- info: 'Wychelean.KEM.MLKEM.ntt_nttInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_nttInv

/-- info: 'Wychelean.KEM.MLKEM.ntt_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_smul

/-- info: 'Wychelean.KEM.MLKEM.ntt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_add

/-- info: 'Wychelean.KEM.MLKEM.ntt_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_sub

/-- info: 'Wychelean.KEM.MLKEM.ntt_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_neg

/-- info: 'Wychelean.KEM.MLKEM.ntt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_zero

/-- info: 'Wychelean.KEM.MLKEM.ntt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_one

/-- info: 'Wychelean.KEM.MLKEM.ntt_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.KEM.MLKEM.ntt_mul

/-- info: 'Wychelean.Utils.PolyRing.Residues.ofFlat_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.Utils.PolyRing.Residues.ofFlat_flatten

/-- info: 'Wychelean.Utils.PolyRing.Residues.flatten_ofFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wychelean.Utils.PolyRing.Residues.flatten_ofFlat
