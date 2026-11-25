/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Algebra.TwoTermHomotopyEquivalenceDirectSum
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Conormal modules under principal localization

Source: Stacks Project, Algebra, Lemma 00S6 (lemma-conormal-module-localize)
(blueprint: lem-weil-pbc-conormal-module-principal-localization).
-/

@[expose] public section

universe u v

namespace Algebra.Extension

/-- Stacks Project, Algebra, Lemma 00S6 (lemma-conormal-module-localize).
(blueprint: lem-weil-pbc-conormal-module-principal-localization)
The kernels of the two polynomial presentations give the conormal modules `I/I²` and `J/J²`.
Their scalar actions are the quotient actions supplied by `Extension.Cotangent.module`.

Proof, following the node's six steps:
1. Form `K = NL(α) ⊗[S] S_g` and `NL(β)`. The polynomial differential basis theorem
   (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables) identifies their degree-zero
   terms with free modules of ranks `n` and `m`. The localization-tensor comparison
   (lem-weil-pbc-localization-module-tensor) identifies `K₁` with `(I/I²)_g`.
2. Choose a lift of `g` along `α`. Adjoin a variable mapped to `1/g` to obtain `β'`.
   By lem-weil-pbc-principal-localization-naive-cotangent, its naive cotangent complex
   is isomorphic to `K` plus the complex `S_g → S_g` given by multiplication by `g`.
3. This extra summand is contractible: multiplication by `g⁻¹` is its contracting
   homotopy. Inclusion and projection give a homotopy equivalence between `K` and `NL(β')`.
4. Mathlib's `Generators.defaultHom` supplies comparison maps between `β'` and `β`.
   Its `Hom.sub`, `Cotangent.map_sub_map` and `CotangentSpace.map_sub_map`, applied
   to identity and composite comparison maps, give the four homotopy identities.
5. Compose the chain maps. If `u,v` are the inclusion/projection maps, `φ,ψ` the
   presentation comparison maps, and `h,h',H` the homotopies, use `v₁ h u₀` on `K`
   and `h' + φ₁ H ψ₀` on `NL(β)` to verify both composite homotopy identities.
6. Apply lem-weil-pbc-two-term-homotopy-equivalence-direct-sum to obtain
   `K₁ ⊕ NL(β)₀ ≅ NL(β)₁ ⊕ K₀`, and substitute the identifications of step 1.
-/
theorem conormalModule_principalLocalization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (g : S) (n m : ℕ)
    (α : MvPolynomial (Fin n) R →ₐ[R] S) (hα : Function.Surjective α)
    (β : MvPolynomial (Fin m) R →ₐ[R] Localization.Away g)
    (hβ : Function.Surjective β) :
    Nonempty
      ((LocalizedModule.Away g (ofSurjective α hα).Cotangent ×
          (Fin m → Localization.Away g)) ≃ₗ[Localization.Away g]
        ((ofSurjective β hβ).Cotangent × (Fin n → Localization.Away g))) := by
  classical
  let T := Localization.Away g
  have heα : MvPolynomial.aeval (α ∘ MvPolynomial.X) = α := by ext; simp
  -- Keep the original algebra action and section, so the associated extension is
  -- definitionally `ofSurjective α hα` rather than merely isomorphic to it.
  let P : Algebra.Generators R S (Fin n) :=
    { val := α ∘ MvPolynomial.X
      σ' := fun x ↦ (hα x).choose
      aeval_val_σ' := by intro x; rw [heα]; exact (hα x).choose_spec
      algebra := α.toAlgebra
      algebraMap_eq := congrArg AlgHom.toRingHom heα.symm }
  let Q := (Algebra.Generators.localizationAway T g).comp P
  have hf : algebraMap P.Ring S (P.σ g) = g := P.toExtension.algebraMap_σ g
  obtain ⟨_, _, r, _, e1, e2, e0, _, _, _, hcomm, _, _⟩ :=
    P.principal_localization_naive_cotangent g (P.σ g) hf (Bg := T)
  have heβ : MvPolynomial.aeval (β ∘ MvPolynomial.X) = β := by ext; simp
  let V : Algebra.Generators R T (Fin m) :=
    { val := β ∘ MvPolynomial.X
      σ' := fun x ↦ (hβ x).choose
      aeval_val_σ' := by intro x; rw [heβ]; exact (hβ x).choose_spec
      algebra := β.toAlgebra
      algebraMap_eq := congrArg AlgHom.toRingHom heβ.symm }
  -- Comparison homotopies come directly from Mathlib, without a new theorem.
  let φ := (Q.defaultHom V).toExtensionHom
  let ψ := (V.defaultHom Q).toExtensionHom
  let h := (Hom.id Q.toExtension).sub (ψ.comp φ)
  let h' := (Hom.id V.toExtension).sub (φ.comp ψ)
  have hφ := CotangentSpace.map_comp_cotangentComplex φ
  have hψ := CotangentSpace.map_comp_cotangentComplex ψ
  have hA1 : LinearMap.id - Cotangent.map ψ ∘ₗ Cotangent.map φ =
      h ∘ₗ Q.toExtension.cotangentComplex := by
    simpa [h, Cotangent.map_id, Cotangent.map_comp] using
      Cotangent.map_sub_map (Hom.id Q.toExtension) (ψ.comp φ)
  have hA0 : LinearMap.id - CotangentSpace.map ψ ∘ₗ CotangentSpace.map φ =
      Q.toExtension.cotangentComplex ∘ₗ h := by
    simpa [h, CotangentSpace.map_id, CotangentSpace.map_comp] using
      CotangentSpace.map_sub_map (Hom.id Q.toExtension) (ψ.comp φ)
  have hB1 : LinearMap.id - Cotangent.map φ ∘ₗ Cotangent.map ψ =
      h' ∘ₗ V.toExtension.cotangentComplex := by
    simpa [h', Cotangent.map_id, Cotangent.map_comp] using
      Cotangent.map_sub_map (Hom.id V.toExtension) (φ.comp ψ)
  have hB0 : LinearMap.id - CotangentSpace.map φ ∘ₗ CotangentSpace.map ψ =
      V.toExtension.cotangentComplex ∘ₗ h' := by
    simpa [h', CotangentSpace.map_id, CotangentSpace.map_comp] using
      CotangentSpace.map_sub_map (Hom.id V.toExtension) (φ.comp ψ)
  let F := P.toExtension.cotangentComplex.baseChange T
  let D := Q.toExtension.cotangentComplex
  let E := V.toExtension.cotangentComplex
  obtain ⟨c, hc⟩ := IsLocalization.Away.algebraMap_isUnit (S := T) g
  have hd (x) : e0 (D x) = (F (e1 x).1, algebraMap S T g * (e1 x).2) := by
    obtain ⟨⟨a, b⟩, rfl⟩ := e1.symm.surjective x
    rw [hcomm, e0.apply_symm_apply, e1.apply_symm_apply]
  -- Contract the invertible rank-one summand.
  let u1 := e1.symm.toLinearMap.comp (LinearMap.inl T _ T)
  let u0 := e0.symm.toLinearMap.comp (LinearMap.inl T _ T)
  let v1 := (LinearMap.fst T _ T).comp e1.toLinearMap
  let v0 := (LinearMap.fst T _ T).comp e0.toLinearMap
  let k : ((TensorProduct S T P.toExtension.CotangentSpace) × T) →ₗ[T]
      ((TensorProduct S T P.toExtension.Cotangent) × T) :=
    (LinearMap.inr T _ T).comp
      (((↑c⁻¹ : T) • LinearMap.id).comp (LinearMap.snd T _ T))
  let H := e1.symm.toLinearMap.comp (k.comp e0.toLinearMap)
  have hu1 (x) : D (u1 x) = u0 (F x) := by
    simpa [u1, u0, F, D] using hcomm x 0
  have hv1 (x) : F (v1 x) = v0 (D x) := by
    exact (congrArg Prod.fst (hd x)).symm
  have hr1 (x) : v1 (u1 x) = x := by simp [v1, u1]
  have hr0 (x) : v0 (u0 x) = x := by simp [v0, u0]
  have hH1 (x) : x - u1 (v1 x) = H (D x) := by
    apply e1.injective
    simp only [map_sub]
    simp only [u1, v1, H, k, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.inl_apply, LinearMap.fst_apply, hd,
      LinearMap.inr_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.snd_apply]
    apply Prod.ext <;> simp [← hc, smul_eq_mul, ← mul_assoc]
  have hH0 (x) : x - u0 (v0 x) = D (H x) := by
    apply e0.injective
    simp only [map_sub]
    simp only [u0, v0, H, k, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.inl_apply, LinearMap.fst_apply, hd,
      LinearMap.inr_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.snd_apply]
    apply Prod.ext <;> simp [← hc, smul_eq_mul, ← mul_assoc]
  -- Compose the retract with the presentation comparison.
  let a1 := (Cotangent.map φ).comp u1
  let a0 := (CotangentSpace.map φ).comp u0
  let b1 := v1.comp (Cotangent.map ψ)
  let b0 := v0.comp (CotangentSpace.map ψ)
  let HK := v1.comp (h.comp u0)
  let HB := h' + (Cotangent.map φ).comp (H.comp (CotangentSpace.map ψ))
  have hφx (x) : E (Cotangent.map φ x) = CotangentSpace.map φ (D x) :=
    (DFunLike.congr_fun hφ x).symm
  have hψx (x) : D (Cotangent.map ψ x) = CotangentSpace.map ψ (E x) :=
    (DFunLike.congr_fun hψ x).symm
  have ha : E.comp a1 = a0.comp F := by
    apply LinearMap.ext
    intro x
    change E (Cotangent.map φ (u1 x)) = CotangentSpace.map φ (u0 (F x))
    rw [hφx, hu1]
  have hb : F.comp b1 = b0.comp E := by
    apply LinearMap.ext
    intro x
    change F (v1 (Cotangent.map ψ x)) = v0 (CotangentSpace.map ψ (E x))
    rw [hv1, hψx]
  have hK1 : LinearMap.id - b1.comp a1 = HK.comp F := by
    apply LinearMap.ext
    intro x
    change x - v1 (Cotangent.map ψ (Cotangent.map φ (u1 x))) =
      v1 (h (u0 (F x)))
    have hx : u1 x - Cotangent.map ψ (Cotangent.map φ (u1 x)) = h (D (u1 x)) :=
      DFunLike.congr_fun hA1 (u1 x)
    have hy := congrArg v1 hx
    rw [map_sub, hr1, hu1] at hy
    exact hy
  have hK0 : LinearMap.id - b0.comp a0 = F.comp HK := by
    apply LinearMap.ext
    intro x
    change x - v0 (CotangentSpace.map ψ (CotangentSpace.map φ (u0 x))) =
      F (v1 (h (u0 x)))
    have hx : u0 x - CotangentSpace.map ψ (CotangentSpace.map φ (u0 x)) =
        D (h (u0 x)) := DFunLike.congr_fun hA0 (u0 x)
    have hy := congrArg v0 hx
    rw [map_sub, hr0, ← hv1] at hy
    exact hy
  have hV1 : LinearMap.id - a1.comp b1 = HB.comp E := by
    apply LinearMap.ext
    intro x
    change x - Cotangent.map φ (u1 (v1 (Cotangent.map ψ x))) =
      h' (E x) + Cotangent.map φ (H (CotangentSpace.map ψ (E x)))
    have hx : x - Cotangent.map φ (Cotangent.map ψ x) = h' (E x) :=
      DFunLike.congr_fun hB1 x
    rw [← hψx, ← hH1, ← hx, map_sub]
    abel
  have hV0 : LinearMap.id - a0.comp b0 = E.comp HB := by
    apply LinearMap.ext
    intro x
    change x - CotangentSpace.map φ (u0 (v0 (CotangentSpace.map ψ x))) =
      E (h' x + Cotangent.map φ (H (CotangentSpace.map ψ x)))
    have hx : x - CotangentSpace.map φ (CotangentSpace.map ψ x) = E (h' x) :=
      DFunLike.congr_fun hB0 x
    rw [map_add, hφx, ← hH0, ← hx]
    rw [map_sub]
    abel
  obtain ⟨e⟩ := Module.prod_linearEquiv_of_twoTermHomotopy T _ _ _ _ F E
    a1 a0 b1 b0 ha hb HK HB hK1 hK0 hV1 hV0
  -- Identify the three terms with the modules in the statement.
  let ea := (P.cotangentSpaceBasis.baseChange T).equivFun
  let eb := V.cotangentSpaceBasis.equivFun
  let el := (LocalizedModule.isBaseChange (Submonoid.powers g)
    P.toExtension.Cotangent).equiv
  have result : Nonempty
      ((LocalizedModule.Away g P.toExtension.Cotangent × (Fin m → T)) ≃ₗ[T]
        (V.toExtension.Cotangent × (Fin n → T))) :=
    ⟨(el.symm.prodCongr eb.symm).trans
      (e.trans ((LinearEquiv.refl T _).prodCongr ea))⟩
  exact result

end Algebra.Extension
