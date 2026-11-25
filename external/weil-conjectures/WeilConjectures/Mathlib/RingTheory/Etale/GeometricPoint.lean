/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Points of algebras with values in an algebraically closed field

Let `A` be a commutative ring, `Ω` a field and `φ : A →+* Ω`. For an `A`-algebra `B`, a
*point of `B` over `φ`* is a ring homomorphism `t : B →+* Ω` extending `φ`
(`RingHom.PointsOver φ B`). Geometrically, `φ` is a point `Spec Ω ⟶ Spec A` and the points of
`B` over `φ` are the lifts `Spec Ω ⟶ Spec B` of it.

A point `t` determines the prime `ker t` of `B`, which lies over `ker φ`, together with an
embedding of the residue field `κ(ker t)` into `Ω` (`RingHom.residueFieldLift`). Conversely,
when `Ω` is algebraically closed and `B` is integral over `A`, every prime of `B` lying over
`ker φ` is the kernel of a point over `φ` (`RingHom.exists_pointsOver_ker_eq`), and a point is
determined by its kernel as soon as the residue field extension at that kernel is purely
inseparable (`RingHom.PointsOver.ext_of_ker_eq_of_isPurelyInseparable`); if moreover the point
is the only one with its kernel, the residue field extension is purely inseparable
(`RingHom.PointsOver.isPurelyInseparable_of_forall_eq`).

Points are compatible with base change: the points of `A' ⊗[A] B` over an extension `φ'` of
`φ` to `A'` are the points of `B` over `φ` (`RingHom.PointsOver.tensorEquiv`), and for `B`
finite over `A` there are only finitely many points over `φ` (`RingHom.PointsOver.finite`).

## Main definitions

- `RingHom.PointsOver`: the points of `B` over `φ`.
- `RingHom.residueFieldLift`: the embedding `κ(ker t) →+* Ω` induced by a point `t`.
- `RingHom.PointsOver.tensorEquiv`: points are compatible with base change.

-/

@[expose] public section

universe u v w

open TensorProduct

namespace RingHom

section ResidueFieldLift

variable {A : Type u} [CommRing A] {Ω : Type w} [Field Ω]

/-- The kernel of a ring homomorphism into a field is prime. -/
instance ker_isPrime_of_field (t : A →+* Ω) : (RingHom.ker t).IsPrime :=
  RingHom.ker_isPrime t

/-- The embedding of the residue field of `ker t` into `Ω` induced by `t : A →+* Ω`. -/
noncomputable def residueFieldLift (t : A →+* Ω) : (RingHom.ker t).ResidueField →+* Ω :=
  Ideal.ResidueField.lift _ t le_rfl (fun x hx ↦
    (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.2 (by simpa [Ideal.primeCompl] using hx)))

@[simp]
lemma residueFieldLift_algebraMap (t : A →+* Ω) (x : A) :
    t.residueFieldLift (algebraMap A _ x) = t x :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ x

lemma residueFieldLift_injective (t : A →+* Ω) : Function.Injective t.residueFieldLift :=
  t.residueFieldLift.injective

/-- A ring homomorphism into a field factors through the residue field of its kernel. -/
lemma residueFieldLift_comp_algebraMap (t : A →+* Ω) :
    t.residueFieldLift.comp (algebraMap A _) = t :=
  RingHom.ext (residueFieldLift_algebraMap t)


end ResidueFieldLift

section PointsOver

variable {A : Type u} [CommRing A] {Ω : Type w} [Field Ω] (φ : A →+* Ω)
  (B : Type v) [CommRing B] [Algebra A B]

/-- The points of the `A`-algebra `B` over `φ : A →+* Ω`: the ring homomorphisms `B →+* Ω`
extending `φ`. -/
def PointsOver : Type _ :=
  {t : B →+* Ω // t.comp (algebraMap A B) = φ}

namespace PointsOver

variable {φ B}

instance : CoeFun (PointsOver φ B) (fun _ ↦ B → Ω) := ⟨fun t ↦ t.1⟩

@[ext]
lemma ext {t t' : PointsOver φ B} (h : ∀ b, t b = t' b) : t = t' :=
  Subtype.ext (RingHom.ext h)

lemma comp_algebraMap (t : PointsOver φ B) : t.1.comp (algebraMap A B) = φ := t.2

@[simp]
lemma apply_algebraMap (t : PointsOver φ B) (a : A) : t (algebraMap A B a) = φ a :=
  RingHom.congr_fun t.2 a

/-- The kernel of a point of `B` over `φ` lies over the kernel of `φ`. -/
lemma ker_liesOver (t : PointsOver φ B) : (RingHom.ker t.1).LiesOver (RingHom.ker φ) :=
  ⟨by rw [Ideal.under, RingHom.comap_ker, t.2]⟩

lemma under_ker (t : PointsOver φ B) : (RingHom.ker t.1).under A = RingHom.ker φ :=
  (ker_liesOver t).over.symm

/-- The point of `B` over `φ` obtained from an embedding of the residue field of a prime `q`
of `B` lying over `ker φ` which extends the embedding of `κ(ker φ)` given by `φ`. -/
noncomputable def ofResidueFieldHom (φ : A →+* Ω) (q : Ideal B) [q.IsPrime]
    [q.LiesOver (RingHom.ker φ)] (ι : q.ResidueField →+* Ω)
    (hι : ι.comp (Ideal.ResidueField.map (RingHom.ker φ) q (algebraMap A B)
      (q.over_def (RingHom.ker φ))) = φ.residueFieldLift) :
    PointsOver φ B :=
  ⟨ι.comp (algebraMap B _), by
    ext a
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A B q.ResidueField]
    rw [IsScalarTower.algebraMap_apply A B q.ResidueField,
      ← Ideal.ResidueField.map_algebraMap (RingHom.ker φ) q (algebraMap A B)
        (q.over_def (RingHom.ker φ)), ← RingHom.comp_apply, hι, residueFieldLift_algebraMap]⟩

lemma ker_ofResidueFieldHom (φ : A →+* Ω) (q : Ideal B) [q.IsPrime] [q.LiesOver (RingHom.ker φ)]
    (ι : q.ResidueField →+* Ω)
    (hι : ι.comp (Ideal.ResidueField.map (RingHom.ker φ) q (algebraMap A B)
      (q.over_def (RingHom.ker φ))) = φ.residueFieldLift) :
    RingHom.ker (ofResidueFieldHom φ q ι hι).1 = q := by
  ext b
  simp only [ofResidueFieldHom, RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff ι ι.injective,
    Ideal.algebraMap_residueField_eq_zero]

end PointsOver

end PointsOver

end RingHom

namespace RingHom.PointsOver

section Lift

variable {A : Type u} [CommRing A] {Ω : Type w} [Field Ω] {φ : A →+* Ω}
  {B : Type v} [CommRing B] [Algebra A B]

/-- The embedding of the residue field of a prime `q` of `B` into `Ω` induced by a point `t`
of `B` over `φ` with kernel `q`. -/
noncomputable def residueFieldLift (t : PointsOver φ B) (q : Ideal B) [q.IsPrime]
    (hq : RingHom.ker t.1 = q) : q.ResidueField →+* Ω :=
  Ideal.ResidueField.lift q t.1 hq.ge (fun x hx ↦
    (IsUnit.mem_submonoid_iff _).2 (isUnit_iff_ne_zero.2 (by
      simpa [Ideal.primeCompl, ← hq, RingHom.mem_ker] using hx)))

@[simp]
lemma residueFieldLift_algebraMap (t : PointsOver φ B) (q : Ideal B) [q.IsPrime]
    (hq : RingHom.ker t.1 = q) (b : B) :
    t.residueFieldLift q hq (algebraMap B _ b) = t b :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ b

/-- The residue field embedding of a point restricts to the one of `φ`. -/
lemma residueFieldLift_comp_map (t : PointsOver φ B) (q : Ideal B) [q.IsPrime]
    (hq : RingHom.ker t.1 = q) [q.LiesOver (RingHom.ker φ)] :
    (t.residueFieldLift q hq).comp (Ideal.ResidueField.map (RingHom.ker φ) q (algebraMap A B)
      (q.over_def (RingHom.ker φ))) = φ.residueFieldLift := by
  refine Ideal.ResidueField.ringHom_ext ?_
  ext a
  simp

/-- A point is determined by the residue field embedding of its kernel. -/
lemma ext_of_residueFieldLift {t t' : PointsOver φ B} (q : Ideal B) [q.IsPrime]
    (hq : RingHom.ker t.1 = q) (hq' : RingHom.ker t'.1 = q)
    (h : t.residueFieldLift q hq = t'.residueFieldLift q hq') : t = t' := by
  ext b
  rw [← residueFieldLift_algebraMap t q hq, ← residueFieldLift_algebraMap t' q hq', h]

/-- **Points with the same kernel agree when the residue field extension is purely
inseparable.** -/
lemma ext_of_ker_eq_of_isPurelyInseparable {t t' : PointsOver φ B} (q : Ideal B) [q.IsPrime]
    [q.LiesOver (RingHom.ker φ)] (hq : RingHom.ker t.1 = q) (hq' : RingHom.ker t'.1 = q)
    (hpi : (Ideal.ResidueField.map (RingHom.ker φ) q (algebraMap A B)
      (q.over_def (RingHom.ker φ))).IsPurelyInseparable) : t = t' := by
  refine ext_of_residueFieldLift q hq hq' ?_
  let := (Ideal.ResidueField.map (RingHom.ker φ) q (algebraMap A B)
    (q.over_def (RingHom.ker φ))).toAlgebra
  let := φ.residueFieldLift.toAlgebra
  have : IsPurelyInseparable (RingHom.ker φ).ResidueField q.ResidueField := hpi
  let ι : q.ResidueField →ₐ[(RingHom.ker φ).ResidueField] Ω :=
    { t.residueFieldLift q hq with
      commutes' := fun x ↦ RingHom.congr_fun (t.residueFieldLift_comp_map q hq) x }
  let ι' : q.ResidueField →ₐ[(RingHom.ker φ).ResidueField] Ω :=
    { t'.residueFieldLift q hq' with
      commutes' := fun x ↦ RingHom.congr_fun (t'.residueFieldLift_comp_map q hq') x }
  exact congrArg AlgHom.toRingHom (Subsingleton.elim ι ι')

/-- Variant of `RingHom.PointsOver.ext_of_ker_eq_of_isPurelyInseparable` for a prime `p` equal
to the kernel of `φ`. -/
lemma ext_of_ker_eq_of_isPurelyInseparable' {t t' : PointsOver φ B} (p : Ideal A) [p.IsPrime]
    (hp : RingHom.ker φ = p) (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hq : RingHom.ker t.1 = q) (hq' : RingHom.ker t'.1 = q)
    (hpi : (Ideal.ResidueField.map p q (algebraMap A B) (q.over_def p)).IsPurelyInseparable) :
    t = t' := by
  subst hp
  exact ext_of_ker_eq_of_isPurelyInseparable q hq hq' hpi

end Lift

section Exists

variable {A : Type u} [CommRing A] {Ω : Type w} [Field Ω] [IsAlgClosed Ω] {φ : A →+* Ω}
  {B : Type v} [CommRing B] [Algebra A B]

/-- **Every prime over the kernel of `φ` is the kernel of a point**, for `B` integral over `A`
and `Ω` algebraically closed. -/
lemma exists_ker_eq [Algebra.IsIntegral A B] (q : Ideal B) [q.IsPrime]
    [q.LiesOver (RingHom.ker φ)] : ∃ t : PointsOver φ B, RingHom.ker t.1 = q := by
  let := Localization.AtPrime.algebraOfLiesOver (RingHom.ker φ) q
  let := φ.residueFieldLift.toAlgebra
  have : Algebra.IsAlgebraic (RingHom.ker φ).ResidueField q.ResidueField := inferInstance
  let ι : q.ResidueField →ₐ[(RingHom.ker φ).ResidueField] Ω := IsAlgClosed.lift
  refine ⟨ofResidueFieldHom φ q ι.toRingHom ?_, ker_ofResidueFieldHom φ q _ _⟩
  refine Ideal.ResidueField.ringHom_ext ?_
  ext a
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  rw [← IsScalarTower.algebraMap_apply A B q.ResidueField,
    IsScalarTower.algebraMap_apply A (RingHom.ker φ).ResidueField q.ResidueField,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ι.commutes]
  rfl

/-- **A point which is the only one with its kernel has purely inseparable residue field
extension**, for `Ω` algebraically closed. -/
lemma isPurelyInseparable_of_forall_eq [Algebra.IsIntegral A B] (t : PointsOver φ B)
    (h : ∀ t' : PointsOver φ B, RingHom.ker t'.1 = RingHom.ker t.1 → t' = t) :
    (Ideal.ResidueField.map (RingHom.ker φ) (RingHom.ker t.1) (algebraMap A B)
      (t.under_ker).symm).IsPurelyInseparable := by
  have := t.ker_liesOver
  let := Localization.AtPrime.algebraOfLiesOver (RingHom.ker φ) (RingHom.ker t.1)
  have e : Ideal.ResidueField.map (RingHom.ker φ) (RingHom.ker t.1) (algebraMap A B)
      (t.under_ker).symm = algebraMap (RingHom.ker φ).ResidueField (RingHom.ker t.1).ResidueField :=
    rfl
  rw [e, RingHom.isPurelyInseparable_algebraMap_iff]
  let := φ.residueFieldLift.toAlgebra
  rw [isPurelyInseparable_iff_subsingleton_emb]
  refine (Field.embEquivOfIsAlgClosed (RingHom.ker φ).ResidueField (RingHom.ker t.1).ResidueField
    Ω).subsingleton_congr.2 ⟨fun f g ↦ ?_⟩
  -- `f` and `g` are the residue field embeddings of two points over `φ` with kernel `ker t`.
  have key : ∀ f : (RingHom.ker t.1).ResidueField →ₐ[(RingHom.ker φ).ResidueField] Ω,
      (ofResidueFieldHom φ (RingHom.ker t.1) f.toRingHom (by
        refine Ideal.ResidueField.ringHom_ext ?_
        ext a
        simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
        rw [← IsScalarTower.algebraMap_apply A B (RingHom.ker t.1).ResidueField,
          IsScalarTower.algebraMap_apply A (RingHom.ker φ).ResidueField
            (RingHom.ker t.1).ResidueField, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f.commutes]
        rfl)) = t :=
    fun f ↦ h _ (ker_ofResidueFieldHom φ _ _ _)
  have hfg := (key f).trans (key g).symm
  refine AlgHom.toRingHom_injective (Ideal.ResidueField.ringHom_ext ?_)
  ext b
  exact congrArg (fun t : PointsOver φ B ↦ t b) hfg

/-- Variant of `RingHom.PointsOver.isPurelyInseparable_of_forall_eq` for primes `p`, `q` equal to
the kernels of `φ` and `t`. -/
lemma isPurelyInseparable_of_forall_eq' [Algebra.IsIntegral A B] (t : PointsOver φ B)
    (h : ∀ t' : PointsOver φ B, RingHom.ker t'.1 = RingHom.ker t.1 → t' = t)
    (p : Ideal A) [p.IsPrime] (hp : RingHom.ker φ = p) (q : Ideal B) [q.IsPrime]
    (hq : RingHom.ker t.1 = q) (hpq : p = q.comap (algebraMap A B)) :
    (Ideal.ResidueField.map p q (algebraMap A B) hpq).IsPurelyInseparable := by
  subst hp hq
  exact isPurelyInseparable_of_forall_eq t h

end Exists

end RingHom.PointsOver

namespace RingHom.PointsOver

section BaseChange

variable {A : Type u} [CommRing A] {Ω : Type w} [Field Ω] {φ : A →+* Ω}
  {A' : Type*} [CommRing A'] [Algebra A A'] {φ' : A' →+* Ω}
  (hφ' : φ'.comp (algebraMap A A') = φ) {B : Type v} [CommRing B] [Algebra A B]

/-- The point of `A' ⊗[A] B` over `φ'` induced by a point of `B` over `φ`, for `φ'` an
extension of `φ` to `A'`. -/
noncomputable def tensor (t : PointsOver φ B) : PointsOver φ' (A' ⊗[A] B) :=
  letI := φ.toAlgebra
  let f : A' →ₐ[A] Ω := { φ' with commutes' := RingHom.congr_fun hφ' }
  let g : B →ₐ[A] Ω := { t.1 with commutes' := t.apply_algebraMap }
  ⟨(Algebra.TensorProduct.productMap f g).toRingHom, by
    ext a'
    change Algebra.TensorProduct.productMap f g (a' ⊗ₜ 1) = φ' a'
    simp [f]⟩

@[simp]
lemma tensor_tmul (t : PointsOver φ B) (a' : A') (b : B) :
    t.tensor hφ' (a' ⊗ₜ b) = φ' a' * t b := by
  let := φ.toAlgebra
  exact Algebra.TensorProduct.productMap_apply_tmul _ _ a' b

@[simp]
lemma tensor_includeRight (t : PointsOver φ B) (b : B) :
    t.tensor hφ' (Algebra.TensorProduct.includeRight b) = t b := by
  simp [Algebra.TensorProduct.includeRight_apply]

lemma tensor_comp_includeRight (t : PointsOver φ B) :
    (t.tensor hφ').1.comp Algebra.TensorProduct.includeRight.toRingHom = t.1 :=
  RingHom.ext (tensor_includeRight hφ' t)

/-- The point of `B` over `φ` obtained by restricting a point of `A' ⊗[A] B` over `φ'`. -/
def restrictTensor (t : PointsOver φ' (A' ⊗[A] B)) : PointsOver φ B :=
  ⟨t.1.comp Algebra.TensorProduct.includeRight.toRingHom, by
    have h : Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap A B) =
        (algebraMap A' (A' ⊗[A] B)).comp (algebraMap A A') := by
      ext a
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [RingHom.comp_assoc, h, ← RingHom.comp_assoc, t.2, hφ']⟩

@[simp]
lemma restrictTensor_apply (t : PointsOver φ' (A' ⊗[A] B)) (b : B) :
    restrictTensor hφ' t b = t (Algebra.TensorProduct.includeRight b) := rfl

/-- **Points are compatible with base change**: the points of `A' ⊗[A] B` over `φ'` are the
points of `B` over `φ`. -/
noncomputable def tensorEquiv : PointsOver φ' (A' ⊗[A] B) ≃ PointsOver φ B where
  toFun := restrictTensor hφ'
  invFun t := t.tensor hφ'
  left_inv t := by
    let := φ.toAlgebra
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul a' b =>
      have h : a' ⊗ₜ[A] b =
          algebraMap A' (A' ⊗[A] B) a' * Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [tensor_tmul, restrictTensor_apply, h, map_mul, t.apply_algebraMap]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv t := by
    ext b
    simp

@[simp]
lemma tensorEquiv_apply (t : PointsOver φ' (A' ⊗[A] B)) :
    tensorEquiv hφ' t = restrictTensor hφ' t := rfl

@[simp]
lemma tensorEquiv_symm_apply (t : PointsOver φ B) :
    (tensorEquiv hφ').symm t = t.tensor hφ' := rfl

lemma ker_tensor_comap_includeRight (t : PointsOver φ B) :
    (RingHom.ker (t.tensor hφ').1).comap Algebra.TensorProduct.includeRight.toRingHom =
      RingHom.ker t.1 := by
  rw [RingHom.comap_ker, tensor_comp_includeRight]

end BaseChange

section Finite

variable {A : Type u} [CommRing A] {Ω : Type w} [Field Ω] {φ : A →+* Ω}
  {B : Type v} [CommRing B] [Algebra A B]

/-- The points of an `Ω`-algebra `C` over the identity of `Ω` are the `Ω`-algebra
homomorphisms `C →ₐ[Ω] Ω`. -/
def equivAlgHom {C : Type v} [CommRing C] [Algebra Ω C] :
    PointsOver (RingHom.id Ω) C ≃ (C →ₐ[Ω] Ω) where
  toFun t := { t.1 with commutes' := fun x ↦ t.apply_algebraMap x }
  invFun f := ⟨f.toRingHom, by ext; simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Finiteness of the points**: a finite `A`-algebra has finitely many points over `φ`. -/
instance finite [Module.Finite A B] : _root_.Finite (PointsOver φ B) := by
  let := φ.toAlgebra
  have h : (RingHom.id Ω).comp (algebraMap A Ω) = φ := RingHom.id_comp _
  have : _root_.Finite (PointsOver (RingHom.id Ω) (Ω ⊗[A] B)) :=
    _root_.Finite.of_equiv _ (equivAlgHom (C := Ω ⊗[A] B)).symm
  exact _root_.Finite.of_equiv _ (tensorEquiv h)

end Finite

end RingHom.PointsOver

namespace RingHom.PointsOver

section Tower

variable {A : Type u} [CommRing A] {Ω : Type w} [Field Ω] {φ : A →+* Ω}
  {A' : Type*} [CommRing A'] [Algebra A A'] {φ' : A' →+* Ω}
  (hφ' : φ'.comp (algebraMap A A') = φ)
  {A'' : Type*} [CommRing A''] [Algebra A A''] [Algebra A' A''] [IsScalarTower A A' A'']
  {φ'' : A'' →+* Ω}
  {B : Type v} [CommRing B] [Algebra A B]

/-- The point of `A''` over `φ` obtained by restricting `φ''`. -/
lemma comp_algebraMap_of_tower (hφ' : φ'.comp (algebraMap A A') = φ)
    (hφ'' : φ''.comp (algebraMap A' A'') = φ') : φ''.comp (algebraMap A A'') = φ := by
  rw [IsScalarTower.algebraMap_eq A A' A'', ← RingHom.comp_assoc, hφ'', hφ']

variable (hφ'' : φ''.comp (algebraMap A' A'') = φ')

/-- Points are compatible with the transition maps of a tower of extensions of `φ`. -/
lemma tensor_map (t : PointsOver φ B) (x : A' ⊗[A] B) :
    t.tensor (comp_algebraMap_of_tower hφ' hφ'')
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' A'') (AlgHom.id A B) x) =
      t.tensor hφ' x := by
  induction x using TensorProduct.inductionOn with
  | tmul a' b =>
    simp only [Algebra.TensorProduct.map_tmul, tensor_tmul, AlgHom.id_apply,
      IsScalarTower.coe_toAlgHom']
    rw [← RingHom.comp_apply φ'' (algebraMap A' A''), hφ'']
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Points are compatible with `Algebra.TensorProduct.cancelBaseChange`. -/
lemma tensor_cancelBaseChange (t : PointsOver φ B) (x : A'' ⊗[A'] (A' ⊗[A] B)) :
    t.tensor (comp_algebraMap_of_tower hφ' hφ'')
      (Algebra.TensorProduct.cancelBaseChange A A' A'' A'' B x) =
      (t.tensor hφ').tensor hφ'' x := by
  induction x using TensorProduct.inductionOn with
  | tmul a'' y =>
    induction y using TensorProduct.inductionOn with
    | tmul a' b =>
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      simp only [tensor_tmul, Algebra.smul_def, map_mul]
      rw [← RingHom.comp_apply φ'' (algebraMap A' A''), hφ'']
      ring
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tower

end RingHom.PointsOver
