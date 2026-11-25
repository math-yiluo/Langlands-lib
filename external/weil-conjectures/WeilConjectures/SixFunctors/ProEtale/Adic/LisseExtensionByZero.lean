/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.LocalVanishing

/-!
# Global sections of the extension by zero of a lisse sheaf

Let `j : Y ⟶ X` be an open immersion of a connected noetherian scheme `Y`, and `H` a lisse
`ℓ`-adic sheaf on `Y`. If some point of `X` outside `Y` is a specialization of a point of `Y`,
then `j_! H` has no nonzero global section
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek`).

Indeed a global section `b` of `j_! H` vanishes on a weakly étale neighbourhood `V ⟶ X` of the
boundary point `z` (`AlgebraicGeometry.ProEtale.exists_map_eq_zero_openImmersionLowerShriek`).
Flat morphisms lift generizations, so `V` also contains a point over a point `y` of `Y`
specializing to `z`; the stalk of `b` at a geometric point there vanishes. So the restriction
`b|_Y` of `b`, a section of the lisse sheaf `H`, has a vanishing stalk, hence vanishes on the
connected scheme `Y`
(`IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero_of_preconnectedSpace`).
Finally the restriction `Γ(X, j_! H) ⟶ Γ(Y, j^* j_! H)` is injective, as the unit
`j_! H ⟶ j_* j^* j_! H` is a monomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- The restriction `Γ(X, j_! H) ⟶ Γ(Y, j^* j_! H)` of global sections of an extension by zero
is injective: the unit `j_! H ⟶ j_* j^* j_! H` is a monomorphism. -/
lemma injective_globalSectionsToUpperStar_adicOpenImmersionLowerShriek (H : AdicSheaf l Y) :
    Function.Injective
      ((globalSectionsToUpperStar (WeilCoefficients.{u} l) j).app ((j)_!ᵃ[l].obj H).X) := by
  let e : (j)_!open[WeilCoefficients.{u} l].obj H.X ≅ ((j)_!ᵃ[l].obj H).X :=
    (asIso (adicOpenImmersionLowerShriekComparison l j)).app H
  let u := (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) j).unit
  have hm : Mono (u.app ((j)_!ᵃ[l].obj H).X) := by
    have h := u.naturality e.hom
    have h₀ : Mono (u.app ((j)_!open[WeilCoefficients.{u} l].obj H.X)) :=
      mono_upperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek j _ H.X
    have : Mono (e.hom ≫ u.app ((j)_!ᵃ[l].obj H).X) := by
      erw [h]
      exact mono_comp _ _
    have hu : u.app ((j)_!ᵃ[l].obj H).X = e.inv ≫ e.hom ≫ u.app ((j)_!ᵃ[l].obj H).X := by
      simp
    rw [hu]
    infer_instance
  refine (ModuleCat.mono_iff_injective _).1 ?_
  rw [globalSectionsToUpperStar_app]
  infer_instance

/-- **A lisse sheaf extended by zero has no global section** as soon as a point `z` outside
the connected noetherian open `Y` is a specialization of a point of `Y`: every morphism
`ℚ̄_ℓ ⟶ j_! H` vanishes. -/
theorem IsAdicLisseSheaf.eq_zero_of_hom_adicOpenImmersionLowerShriek [NoetherianSpace Y]
    [PreconnectedSpace Y] {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) {y : Y} {z : X}
    (hz : z ∉ Set.range j.base) (hyz : j.base y ⤳ z)
    (β : AdicSheaf.unit l X ⟶ (j)_!ᵃ[l].obj H) : β = 0 := by
  set A := WeilCoefficients.{u} l
  set N := ((j)_!ᵃ[l].obj H).X
  set b := globalSectionOfModHom β
  let e : (j)_!open[WeilCoefficients.{u} l].obj H.X ≅ ((j)_!ᵃ[l].obj H).X :=
    (asIso (adicOpenImmersionLowerShriekComparison l j)).app H
  set b' := ((Sheaf.Γ _ A).map e.inv).hom b
  obtain ⟨V', f, ⟨w, hw⟩, hσ⟩ := exists_map_eq_zero_openImmersionLowerShriek j H.X
    (V := ProEt.mk (𝟙 X))
    (((Sheaf.ΓNatIsoSheafSections (ProEt.topology X) A (ProEt.isTerminalMkId X)).hom.app
      ((j)_!open[A].obj H.X)).hom b') z hz
  have hf : f = (ProEt.isTerminalMkId X).from V' := (ProEt.isTerminalMkId X).hom_ext _ _
  subst hf
  let g : V'.left ⟶ X := V'.hom
  have : WeaklyEtale g := V'.prop
  -- the restriction of `b` along `V' ⟶ X` vanishes
  have h₁ : ((globalSectionsToUpperStar A g).app _).hom b' = 0 :=
    globalSectionsToUpperStar_apply_eq_zero_of_restrict_eq_zero g b' hσ
  have h₂ : ((globalSectionsToUpperStar A g).app N).hom b = 0 := by
    have hn := congrArg (fun φ ↦ φ.hom b') ((globalSectionsToUpperStar A g).naturality e.hom)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, h₁,
      map_zero] at hn
    have hb : ((Sheaf.Γ _ A).map e.hom).hom b' = b := by
      simp only [b', ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply]
    rw [← hb]
    exact hn
  -- a point of `V'` over a point of `Y` specializing to `z`
  have hw' : g.base w = z := by
    have := MorphismProperty.Over.w ((ProEt.isTerminalMkId X).from V')
    rw [← hw]
    exact (congrArg (fun φ ↦ φ.base w) this).symm
  obtain ⟨w', -, hw'y⟩ := Flat.generalizingMap g (hw' ▸ hyz)
  -- a geometric point there
  let K := AlgebraicClosure (V'.left.residueField w')
  let t : Spec (.of K) ⟶ V'.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (V'.left.residueField w') K)) ≫
      V'.left.fromSpecResidueField w'
  have ht : t.base (IsLocalRing.closedPoint K) = w' := by
    simp only [t, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply w' _
  have hrange : Set.range (t ≫ g).base ⊆ Set.range j.base := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨y, by rw [Scheme.Hom.comp_apply, ht]; exact hw'y.symm⟩
  let s := IsOpenImmersion.lift j (t ≫ g) hrange
  have hs : s ≫ j = t ≫ g := IsOpenImmersion.lift_fac _ _ _
  -- the stalk of `b` at `s ≫ j` vanishes
  have h₃ : ∀ r : Spec (.of K) ⟶ X, r = t ≫ g →
      ((globalSectionsToUpperStar A r).app N).hom b = 0 := by
    rintro r rfl
    have hc := congrArg (fun φ ↦ φ.hom b) (globalSectionsToUpperStar_comp A t g N)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at hc
    have h₂' : ((globalSectionsToUpperStar A t).app ((g)^*[A].obj N)).hom
        (((globalSectionsToUpperStar A g).app N).hom b) = 0 := by
      rw [h₂, map_zero]
    have h₄' := hc.trans h₂'
    refine (ModuleCat.mono_iff_injective ((Sheaf.Γ _ A).map
      ((upperStarComp A t g).hom.app N))).1 inferInstance (h₄'.trans ?_)
    exact (map_zero _).symm
  have h₄ : ((globalSectionsToUpperStar A s).app _).hom
      (((globalSectionsToUpperStar A j).app N).hom b) = 0 := by
    have hc := congrArg (fun φ ↦ φ.hom b) (globalSectionsToUpperStar_comp A s j N)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at hc
    have h₃' : ((Sheaf.Γ _ A).map ((upperStarComp A s j).hom.app N)).hom
        (((globalSectionsToUpperStar A (s ≫ j)).app N).hom b) = 0 := by
      rw [h₃ _ hs, map_zero]
    exact hc.symm.trans h₃'
  -- the restriction of `b` to the connected scheme `Y` vanishes
  let γ := (adicUpperStarUnitIso l j).inv ≫ (j)^*ᵃ[l].map β
  have hlisse : IsAdicLisseSheaf ((j)^*ᵃ[l].obj ((j)_!ᵃ[l].obj H)) :=
    hH.of_iso (asIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app H))
  have hγ : γ = 0 := hlisse.eq_zero_of_globalSectionsToUpperStar_eq_zero_of_preconnectedSpace γ
    K s (by
      have key : globalSectionOfModHom γ = ((globalSectionsToUpperStar A j).app N).hom b :=
        (globalSectionsToUpperStar_globalSectionOfModHom j β).symm
      rw [key]
      exact h₄)
  have h0 {M : AdicSheaf l Y} : globalSectionOfModHom (0 : AdicSheaf.unit l Y ⟶ M) = 0 := by
    rw [globalSectionOfModHom_eq]
    rw [Mod.zero_hom, Functor.map_zero]
    rfl
  have h₅ : ((globalSectionsToUpperStar A j).app N).hom b = 0 := by
    rw [globalSectionsToUpperStar_globalSectionOfModHom]
    change globalSectionOfModHom γ = 0
    rw [hγ, h0]
  have h₆ : b = 0 := injective_globalSectionsToUpperStar_adicOpenImmersionLowerShriek j H
    (h₅.trans (map_zero _).symm)
  have h0' : globalSectionOfModHom (0 : AdicSheaf.unit l X ⟶ (j)_!ᵃ[l].obj H) = 0 := by
    rw [globalSectionOfModHom_eq]
    rw [Mod.zero_hom, Functor.map_zero]
    rfl
  exact (bijective_globalSectionOfModHom _).1 (h₆.trans h0'.symm)

/-- **A lisse sheaf extended by zero has no global section** as soon as a point `z` outside
the connected noetherian open `Y` is a specialization of a point of `Y`. -/
theorem IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek [NoetherianSpace Y]
    [PreconnectedSpace Y] {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) {y : Y} {z : X}
    (hz : z ∉ Set.range j.base) (hyz : j.base y ⤳ z) :
    IsZero ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((j)_!ᵃ[l].obj H).X) := by
  have : Subsingleton ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((j)_!ᵃ[l].obj H).X) := by
    refine ⟨fun a c ↦ ?_⟩
    obtain ⟨α, rfl⟩ := (bijective_globalSectionOfModHom _).2 a
    obtain ⟨δ, rfl⟩ := (bijective_globalSectionOfModHom _).2 c
    rw [hH.eq_zero_of_hom_adicOpenImmersionLowerShriek j hz hyz α,
      hH.eq_zero_of_hom_adicOpenImmersionLowerShriek j hz hyz δ]
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.ProEtale
