/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian

/-!
# Lisse sheaves with vanishing geometric stalks

A lisse `ℓ`-adic sheaf `H` on an arbitrary scheme `Y` vanishes as soon as, over every point `y`
of `Y`, there is a geometric point `s : Spec K ⟶ Y`, with `K` algebraically closed and allowed
to depend on `y`, at which the stalk `Γ(Spec K, s^* H)` vanishes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_of_forall_subsingleton_stalk`). Unlike
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_of_subsingleton_globalSections_upperStar`,
no Noetherian hypothesis and no common field of definition of the geometric points is needed:
every point is tested directly. This applies to the strict localizations of a scheme of finite
type over a field, whose residue fields do not embed into a single algebraically closed field.

This is the lisse step of the vanishing criterion for constructible sheaves through geometric
stalks, which enters the specialization criterion for lisse sheaves: if all geometric stalks of
an `ℓ`-adic sheaf `H` vanish, then so does its restriction `g^* H` to every `g : Z ⟶ X` along
which it becomes lisse, e.g. to every stratum of a stratification on which `H` is lisse
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_of_forall_subsingleton_stalk`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- **A lisse sheaf with vanishing geometric stalks vanishes.** If over every point `y` of `Y`
there is a geometric point `s : Spec K ⟶ Y` (with `K` algebraically closed, depending on `y`) at
which the stalk of the lisse sheaf `H` vanishes, then `H = 0`. Indeed, on a member `f : V ⟶ Y`
of a trivialising cover with `f^* H ≅ ℚ̄_ℓⁿ` and `V` nonempty, the geometric point over the image
of a point of `V` lifts to `V`, so the stalk would contain `ℚ̄_ℓ` if `n > 0`.

Blueprint `lem-wf-lisse-stalk-vanishing` (1). -/
theorem IsAdicLisseSheaf.isZero_of_forall_subsingleton_stalk {Y : Scheme.{u}}
    {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H)
    (h : ∀ y : Y, ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (s : Spec (.of K) ⟶ Y),
      s.base (IsLocalRing.closedPoint K) = y ∧
      Subsingleton ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj H.X))) :
    IsZero H := by
  classical
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  have hz (i : ι) : IsZero ((f i)^*ᵃ[l].obj H) := by
    by_cases hV : Nonempty (V i)
    · obtain ⟨v⟩ := hV
      suffices h0 : n i = 0 by
        refine IsZero.of_iso ?_ (e i).some
        rw [h0]
        exact ⟨fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext' _ _ fun j ↦ Fin.elim0 j⟩⟩,
          fun _ ↦ ⟨⟨⟨0⟩, fun _ ↦ biproduct.hom_ext _ _ fun j ↦ Fin.elim0 j⟩⟩⟩
      by_contra hpos
      obtain ⟨K, _, _, s, hs, hsub⟩ := h (f i v)
      have := nontrivial_globalSections_upperStar_of_iso (f i) (e i).some
        (Nat.pos_of_ne_zero hpos) s ⟨v, hs.symm⟩
      exact not_subsingleton _ hsub
    · have : IsEmpty (V i) := not_nonempty_iff.1 hV
      exact isZero_adicSheaf_of_isEmpty l _
  have : IsIso (0 : H ⟶ 0) := isIso_of_isIso_adicUpperStar l f hR _ fun i ↦ by
    have hz' : IsZero ((f i)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
    rw [(hz i).eq_of_src ((f i)^*ᵃ[l].map 0) ((hz i).iso hz').hom]
    infer_instance
  exact (isZero_zero _).of_iso (asIso (0 : H ⟶ 0))

/-- **Vanishing of a lisse restriction with vanishing stalks.** Let `H` be an `ℓ`-adic sheaf on
`X` all of whose geometric stalks vanish, and `g : Z ⟶ X` a morphism along which `H` becomes
lisse (e.g. a stratum of a stratification on which `H` is lisse). Then `g^* H = 0`: the stalks
of `g^* H` at the geometric points `Spec κ(z)‾ ⟶ Z` are stalks of `H`.

Blueprint `lem-wf-lisse-stalk-vanishing` (2). -/
theorem isZero_adicUpperStar_of_forall_subsingleton_stalk {X Z : Scheme.{u}}
    {H : AdicSheaf l X} (g : Z ⟶ X) (hg : IsAdicLisseSheaf ((g)^*ᵃ[l].obj H))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ X),
      Subsingleton ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((s)^*[_].obj H.X))) :
    IsZero ((g)^*ᵃ[l].obj H) := by
  refine hg.isZero_of_forall_subsingleton_stalk fun z ↦ ?_
  let s : Spec (.of (AlgebraicClosure (Z.residueField z))) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) _)) ≫ Z.fromSpecResidueField z
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance, s, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply]
    exact Z.fromSpecResidueField_apply z _
  · have := h _ (s ≫ g)
    let e := (Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso
      ((AdicSheaf.forget _).mapIso ((adicUpperStarComp l s g).app H))
    exact @Equiv.subsingleton _ _ ((CategoryTheory.forget _).mapIso e).toEquiv.symm this

end AlgebraicGeometry.ProEtale
