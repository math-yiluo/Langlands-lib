/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.ConormalModulePrincipalLocalization

/-!
# Local comparison of conormals of two polynomial presentations

Source: Stacks Project, Algebra, Tag 00S6 (lemma-conormal-module-localize),
base changed to the local ring as in the last paragraph of Tag 00SC (lemma-lci).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Ideal

attribute [local instance] LocalizedModule.moduleOfIsLocalization

set_option backward.isDefEq.respectTransparency false in
/-- The stable presentation comparison base changed to a prime of the original quotient.
This statement has no complete intersection or dimension hypothesis.

Source: Stacks Project, Algebra, Tag 00S6 (lemma-conormal-module-localize), and
Tag 00SC (lemma-lci), last paragraph, the localization of its displayed isomorphism.
(blueprint: lem-weil-pbc-principal-localization-conormal-at-prime-base-change)

Proof:
1. Apply `Algebra.Extension.conormalModule_principalLocalization` to the quotient
map k[x] → S = k[x]/I and the composite k[y] → T = k[y]/J → S_g.
Both maps are surjective. Their extension kernels are I and J: use the quotient
kernel identity for the first and injectivity of e for the second.
2. `cotangentEquivCotangentKer` and `Ideal.Cotangent.equivOfEq` identify the first
extension conormal with I.Cotangent over k[x]. Surjectivity of k[x] → S extends
this equivalence to an S-linear one. The module-localization universal property
identifies its localization away from g with S_g tensor_S I.Cotangent.
3. The image of g in R = S_q is a unit because g is outside q. Extend S → R
uniquely to S_g → R. Tensor the comparison of step 1 with R over S_g.
For the left conormal term, use the equivalence of step 2, tensor cancellation
R tensor_Sg (S_g tensor_S I.Cotangent) = R tensor_S I.Cotangent,
and the module-localization universal property at q.
4. For the right conormal term use Extension.cotangentEquiv, which identifies
D.Cotangent with S_g tensor_Q D.ker. Tensor cancellation and the kernel equality
identify its base change with R tensor_Q J. The quotient tensor equivalence
T tensor_Q J = J/J², extended from Q to T using quotient surjectivity, and tensor
cancellation identify this with R tensor_T J.Cotangent. All the algebra towers
are the composites of the quotient map, e, and the localization lift; their
commutativity is the lift identity and definitional equality.
5. Tensor distributes over products and finite powers of S_g. Compose these
maps with the left and right conormal identifications to obtain the claimed
R-linear equivalence. The empty-variable case uses the same finite-product maps.
No freeness or cancellation of a free summand is used. -/
theorem principalLocalization_conormal_atPrime_baseChange
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))
    (g : MvPolynomial (Fin n) k ⧸ I) (hg : g ∉ q.asIdeal)
    (m : ℕ) (J : Ideal (MvPolynomial (Fin m) k))
    (e : (MvPolynomial (Fin m) k ⧸ J) ≃ₐ[k] Localization.Away g) :
    let φ : (MvPolynomial (Fin m) k ⧸ J) →+* Localization.AtPrime q.asIdeal :=
      (IsLocalization.Away.lift g
        ((IsLocalization.AtPrime.isUnit_to_map_iff
          (Localization.AtPrime q.asIdeal) q.asIdeal g).mpr hg)).comp e.toRingHom
    letI : Algebra (MvPolynomial (Fin m) k ⧸ J) (Localization.AtPrime q.asIdeal) :=
      φ.toAlgebra
    Nonempty
      ((LocalizedModule q.asIdeal.primeCompl I.Cotangent ×
          (Fin m → Localization.AtPrime q.asIdeal)) ≃ₗ[Localization.AtPrime q.asIdeal]
        ((Localization.AtPrime q.asIdeal ⊗[MvPolynomial (Fin m) k ⧸ J] J.Cotangent) ×
          (Fin n → Localization.AtPrime q.asIdeal))) := by
  classical
  let P := MvPolynomial (Fin n) k
  let Q := MvPolynomial (Fin m) k
  let S := P ⧸ I
  let T := Q ⧸ J
  let B := Localization.Away g
  let R := Localization.AtPrime q.asIdeal
  let α : P →ₐ[k] S := Ideal.Quotient.mkₐ k I
  have hα : Function.Surjective α := Ideal.Quotient.mkₐ_surjective k I
  let β : Q →ₐ[k] B := e.toAlgHom.comp (Ideal.Quotient.mkₐ k J)
  have hβ : Function.Surjective β := e.surjective.comp (Ideal.Quotient.mkₐ_surjective k J)
  let A := Algebra.Extension.ofSurjective α hα
  let D := Algebra.Extension.ofSurjective β hβ
  have hA : A.ker = I := Ideal.Quotient.mkₐ_ker k I
  have hD : D.ker = J := by
    ext x
    change e (Ideal.Quotient.mk J x) = 0 ↔ x ∈ J
    rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]
  let aP : A.Cotangent ≃ₗ[P] I.Cotangent :=
    A.cotangentEquivCotangentKer ≪≫ₗ Ideal.Cotangent.equivOfEq A.ker I hA
  let aS : A.Cotangent ≃ₗ[S] I.Cotangent :=
    aP.extendScalarsOfSurjective (show Function.Surjective (algebraMap P S) from hα)
  let L : LocalizedModule.Away g A.Cotangent ≃ₗ[B] B ⊗[S] A.Cotangent :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) A.Cotangent)
      (TensorProduct.mk S B A.Cotangent 1)).extendScalarsOfIsLocalization
        (Submonoid.powers g) B
  obtain ⟨E⟩ := Algebra.Extension.conormalModule_principalLocalization g n m α hα β hβ
  let hu : IsUnit (algebraMap S R g) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff R q.asIdeal g).mpr hg
  let bR : B →+* R := IsLocalization.Away.lift g hu
  let : Algebra B R := bR.toAlgebra
  have : IsScalarTower S B R := IsScalarTower.of_algebraMap_eq' (by
    exact (IsLocalization.Away.lift_comp g hu).symm)
  dsimp only
  let N : LocalizedModule q.asIdeal.primeCompl I.Cotangent ≃ₗ[R] R ⊗[S] I.Cotangent :=
    (IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl I.Cotangent)
      (TensorProduct.mk S R I.Cotangent 1)).extendScalarsOfIsLocalization
        q.asIdeal.primeCompl R
  let left : R ⊗[B] LocalizedModule.Away g A.Cotangent ≃ₗ[R]
      LocalizedModule q.asIdeal.primeCompl I.Cotangent :=
    LinearEquiv.baseChange B R _ _ L ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange S B R R A.Cotangent ≪≫ₗ
      LinearEquiv.baseChange S R _ _ aS ≪≫ₗ N.symm
  let : Algebra T R := (bR.comp e.toRingHom).toAlgebra
  let : Algebra Q B := D.algebra₂
  let : Algebra Q R := Algebra.compHom R (Ideal.Quotient.mk J)
  have : IsScalarTower Q T R := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Q B R := IsScalarTower.of_algebraMap_eq' rfl
  let dQ : D.ker ≃ₗ[Q] J := LinearEquiv.ofEq _ _ hD
  let right₀ : R ⊗[B] D.Cotangent ≃ₗ[R] R ⊗[Q] J :=
    LinearEquiv.baseChange B R _ _ D.cotangentEquiv.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange Q B R R D.ker ≪≫ₗ
      LinearEquiv.baseChange Q R _ _ dQ
  let jT : T ⊗[Q] J ≃ₗ[T] J.Cotangent :=
    (TensorProduct.quotTensorEquivQuotSMul J J).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let right₁ : R ⊗[T] J.Cotangent ≃ₗ[R] R ⊗[Q] J :=
    LinearEquiv.baseChange T R _ _ jT.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange Q T R R J
  let right := right₀ ≪≫ₗ right₁.symm
  let E' := LinearEquiv.baseChange B R _ _ E
  let pm := TensorProduct.piScalarRight B R R (Fin m)
  let pn := TensorProduct.piScalarRight B R R (Fin n)
  exact ⟨(left.prodCongr pm).symm ≪≫ₗ
    (TensorProduct.prodRight B R R _ _).symm ≪≫ₗ E' ≪≫ₗ
    TensorProduct.prodRight B R R _ _ ≪≫ₗ right.prodCongr pn⟩

end Ideal
