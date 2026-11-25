/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Etale.Kaehler
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent

/-!
# Split conormal sequence of a smooth principal localization

Source: Stacks Project, Smoothing Ring Maps, proofs of Tags 07EZ (part (e)) and 07C6
(blueprint: lem-weil-pbc-smooth-localization-conormal-split).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

variable (R : Type u) [CommRing R] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R))
variable (a : MvPolynomial (Fin n) R ⧸ I)

local notation "A" => (MvPolynomial (Fin n) R ⧸ I)
local notation "B" => Localization.Away a
local notation "M" => LocalizedModule.Away a I.Cotangent

attribute [local instance] LocalizedModule.moduleOfIsLocalization

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The localized conormal differential of a polynomial presentation splits when the localized
quotient is smooth. The two maps are specified by their values on `g mod I²` divided by one
and on the coordinate basis vectors. These values uniquely determine the localized differential
and the map to Kähler differentials. The finite free module is represented by `Fin n → B`,
and the sum of the conormal and differential modules by their product.

Source: Stacks Project, Smoothing Ring Maps, proofs of Tags 07EZ (part (e)) and 07C6
(blueprint: lem-weil-pbc-smooth-localization-conormal-split).

Proof:
1. Use the quotient presentation `P` and adjoin a generator for `1/a` to obtain `Q`.
   The polynomial algebra of `Q` is formally smooth. Smoothness of `B` annihilates its
   first cotangent homology, so Mathlib's `cotangentComplex_injective_iff` makes the
   differential of `Q` injective. The injectivity equivalence of
   `principal_localization_naive_cotangent` transfers this to the base change of `P`.
2. Identify `P`'s conormal module with `I.Cotangent`, then use the universal property of
   module localization to identify its localization with its base change to `B`.
   The base change of the polynomial differential basis identifies the middle module
   with `Fin n → B`. Differentials commute with localization, giving the isomorphism
   `B ⊗[A] Ω[A/R] ≃ Ω[B/R]`. Conjugate the base-changed conormal sequence by these
   three equivalences. Tensor right exactness gives exactness and surjectivity.
   On an equation class its coordinates are the partial derivatives, by
   `cotangentComplex_mk` and `cotangentSpaceBasis_repr_one_tmul`. On a coordinate
   basis vector the quotient map is the differential of the corresponding variable.
3. Smoothness makes `Ω[B/R]` projective. Lift its identity along the surjection to
   obtain a section. `Exact.splitSurjectiveEquiv` gives the product decomposition;
   projection onto its first factor is the left inverse of the conormal differential. -/
theorem smooth_localization_conormal_split
    [Smooth R B] :
    ∃ (d : M →ₗ[B] (Fin n → B)) (π : (Fin n → B) →ₗ[B] KaehlerDifferential R B),
      (∀ (g : I) (i : Fin n),
        d (LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent
          (I.toCotangent g)) i =
            algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.pderiv i (g : _)))) ∧
      (∀ i : Fin n, π (Pi.single i 1) =
        KaehlerDifferential.D R B
          (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i)))) ∧
      (∃ l : (Fin n → B) →ₗ[B] M, l.comp d = LinearMap.id) ∧
      Function.Injective d ∧ Function.Surjective π ∧
      LinearMap.ker π = LinearMap.range d ∧
      (∃ s : KaehlerDifferential R B →ₗ[B] (Fin n → B), π.comp s = LinearMap.id) ∧
      Nonempty ((M × KaehlerDifferential R B) ≃ₗ[B] (Fin n → B)) := by
  classical
  let α := Ideal.Quotient.mkₐ R I
  have hα₀ : MvPolynomial.aeval (α ∘ MvPolynomial.X) = α := by
    ext i
    simp
  let P : Generators R A (Fin n) :=
    { Generators.ofAlgHom α (Ideal.Quotient.mkₐ_surjective R I) with
      algebra := inferInstance
      algebraMap_eq := by
        change (Ideal.Quotient.mk I) = _
        exact congrArg AlgHom.toRingHom hα₀.symm }
  have hα : MvPolynomial.aeval (P.val) = Ideal.Quotient.mkₐ R I := by
    ext i
    simp [P, α, Generators.ofAlgHom, Generators.ofSurjective]
  have hp : P.ker = I := by
    rw [Generators.ker_eq_ker_aeval_val, hα]
    exact Ideal.Quotient.mkₐ_ker R I
  let q : P.toExtension.Cotangent ≃ₗ[MvPolynomial (Fin n) R] I.Cotangent := by
    let q₀ := Extension.cotangentEquivCotangentKer (P := P.toExtension)
    let q₁ := Ideal.Cotangent.equivOfEq P.toExtension.ker I hp
    exact q₀ ≪≫ₗ q₁
  let qA : P.toExtension.Cotangent ≃ₗ[A] I.Cotangent :=
    q.extendScalarsOfSurjective P.algebraMap_surjective
  let Q := (Generators.localizationAway B a).comp P
  have hQ : Function.Injective Q.toExtension.cotangentComplex := by
    have : FormallySmooth R Q.toExtension.Ring :=
      inferInstanceAs (FormallySmooth R (MvPolynomial _ R))
    exact Q.toExtension.cotangentComplex_injective_iff.mpr inferInstance
  have hi : Function.Injective (P.toExtension.cotangentComplex.baseChange B) := by
    obtain ⟨_, _, r, hr, e1, e2, e0, he1, he2, he0, hd, hij, _⟩ :=
      Generators.principal_localization_naive_cotangent P a (P.σ a) (by
        change Ideal.Quotient.mk I (P.σ a) = a
        rw [← Ideal.Quotient.mkₐ_eq_mk R I, ← hα]
        exact P.aeval_val_σ a) (Bg := B)
    exact hij.mpr hQ
  let eM : M ≃ₗ[B] TensorProduct A B P.toExtension.Cotangent :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent)
      (TensorProduct.mk A B I.Cotangent 1)).extendScalarsOfIsLocalization
        (Submonoid.powers a) B |>.trans (LinearEquiv.baseChange A B _ _ qA.symm)
  let b := P.cotangentSpaceBasis.baseChange B
  let eF : (TensorProduct A B P.toExtension.CotangentSpace) ≃ₗ[B] (Fin n → B) :=
    b.equivFun
  let eK := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
  let d : M →ₗ[B] (Fin n → B) :=
    eF.toLinearMap.comp ((P.toExtension.cotangentComplex.baseChange B).comp eM.toLinearMap)
  let π : (Fin n → B) →ₗ[B] KaehlerDifferential R B :=
    eK.toLinearMap.comp ((P.toExtension.toKaehler.baseChange B).comp eF.symm.toLinearMap)
  have hd : Function.Injective d := eF.injective.comp (hi.comp eM.injective)
  have hπ : Function.Surjective π := eK.surjective.comp
    ((LinearMap.lTensor_surjective B P.toExtension.toKaehler_surjective).comp eF.symm.surjective)
  have hex₀ : Function.Exact (P.toExtension.cotangentComplex.baseChange B)
      (P.toExtension.toKaehler.baseChange B) := by
    exact _root_.lTensor_exact B P.toExtension.exact_cotangentComplex_toKaehler
      P.toExtension.toKaehler_surjective
  have hex : Function.Exact d π := by
    apply eK.injective.comp_exact_iff_exact.mpr
    apply (LinearEquiv.conj_exact_iff_exact _ _ eF).mpr
    exact eM.surjective.comp_exact_iff_exact.mpr hex₀
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π
    (LinearMap.id : KaehlerDifferential R B →ₗ[B] KaehlerDifferential R B) hπ
  obtain ⟨e, hef, heg⟩ := hex.splitSurjectiveEquiv hd ⟨s, hs⟩
  have hl : (LinearMap.fst B M (KaehlerDifferential R B)).comp
      (e.toLinearMap.comp d) = LinearMap.id := by
    rw [hef]
    ext x
    simp
  refine ⟨d, π, ?_, ?_, ⟨(LinearMap.fst B M (KaehlerDifferential R B)).comp e.toLinearMap, by
    simpa only [LinearMap.comp_assoc] using hl⟩, hd, hπ, hex.linearMap_ker_eq, ⟨s, hs⟩, ⟨e.symm⟩⟩
  · intro g i
    let y : P.toExtension.ker := ⟨g.val, by
      change g.val ∈ P.ker
      rw [hp]
      exact g.prop⟩
    have hq : qA (Extension.Cotangent.mk y) = I.toCotangent g := by
      change Ideal.Cotangent.equivOfEq P.toExtension.ker I hp
        (P.toExtension.ker.toCotangent y) = I.toCotangent g
      rw [Ideal.Cotangent.equivOfEq_toCotangent]
      congr 1
    have heM : eM (LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent
        (I.toCotangent g)) = TensorProduct.tmul A (1 : B) (Extension.Cotangent.mk y) := by
      change (LinearEquiv.baseChange A B _ _ qA.symm)
        ((IsLocalizedModule.linearEquiv (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent)
          (TensorProduct.mk A B I.Cotangent 1))
            ((LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent)
              (I.toCotangent g))) = _
      rw [IsLocalizedModule.linearEquiv_apply]
      change (LinearEquiv.baseChange A B _ _ qA.symm)
        (TensorProduct.tmul A (1 : B) (I.toCotangent g)) = _
      rw [LinearEquiv.baseChange_tmul, ← hq, qA.symm_apply_apply]
    change eF ((P.toExtension.cotangentComplex.baseChange B)
      (eM ((LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent)
        (I.toCotangent g)))) i = _
    rw [heM, LinearMap.baseChange_tmul, Extension.cotangentComplex_mk]
    change (b.repr (TensorProduct.tmul A (1 : B)
      (TensorProduct.tmul P.toExtension.Ring (1 : A)
        (KaehlerDifferential.D R P.toExtension.Ring y)))) i = _
    rw [Module.Basis.baseChange_repr_tmul, Generators.cotangentSpaceBasis_repr_one_tmul]
    rw [hα]
    simp [y, Algebra.smul_def]
  · intro i
    have heF : eF.symm (Pi.single i 1) = b i := by
      apply eF.injective
      rw [eF.apply_symm_apply]
      ext j
      simp [eF, Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
    change eK ((P.toExtension.toKaehler.baseChange B) (eF.symm (Pi.single i 1))) = _
    rw [heF, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      Generators.toKaehler_cotangentSpaceBasis]
    simp [eK, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
      P, α, Generators.ofAlgHom, Generators.ofSurjective]
end Algebra
