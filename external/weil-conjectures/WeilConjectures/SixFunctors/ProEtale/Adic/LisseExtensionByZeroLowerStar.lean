/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseExtensionByZero

/-!
# Global sections of the extension by zero of a direct image of a lisse sheaf

Let `ι : W ⟶ Y` and `j : Y ⟶ X` be open immersions, with `W` connected and noetherian, and `H` a
lisse `ℓ`-adic sheaf on `W`. If some point of `X` outside `Y` is a specialization of a point of
`W`, then `j_! ι_* H` has no nonzero global section
(`ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek_adicLowerStar`).

The argument is that of
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek`:
a global section `b` of `j_! ι_* H` vanishes near the boundary point `z`, hence its restriction
to `Y`, a section of `ι_* H`, has a vanishing stalk at a geometric point of `W` specializing to
`z`. Its further restriction to `W`, a section of `ι^* ι_* H ≅ H`, therefore vanishes on the
connected scheme `W`; since `ι^* ⊣ ι_*`, a section of `ι_* H` whose restriction to `W` vanishes
is zero, and the restriction `Γ(X, j_! M) ⟶ Γ(Y, j^* j_! M)` is injective.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime] {X Y W : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (ι : W ⟶ Y) [IsOpenImmersion ι]

/-- **The extension by zero of a direct image of a lisse sheaf has no global section** as soon
as a point `z` outside the open `Y` is a specialization of a point of the connected noetherian
open `W ⊆ Y` carrying the lisse sheaf: every morphism `ℚ̄_ℓ ⟶ j_! ι_* H` vanishes. -/
theorem IsAdicLisseSheaf.eq_zero_of_hom_adicOpenImmersionLowerShriek_adicLowerStar
    [NoetherianSpace W] [PreconnectedSpace W] {H : AdicSheaf l W} (hH : IsAdicLisseSheaf H)
    {w : W} {z : X} (hz : z ∉ Set.range j.base) (hwz : j.base (ι.base w) ⤳ z)
    (β : AdicSheaf.unit l X ⟶ (j)_!ᵃ[l].obj ((ι)_*ᵃ[l].obj H)) : β = 0 := by
  set A := WeilCoefficients.{u} l
  let M := (ι)_*ᵃ[l].obj H
  set N := ((j)_!ᵃ[l].obj M).X
  set b := globalSectionOfModHom β
  let e : (j)_!open[WeilCoefficients.{u} l].obj M.X ≅ ((j)_!ᵃ[l].obj M).X :=
    (asIso (adicOpenImmersionLowerShriekComparison l j)).app M
  set b' := ((Sheaf.Γ _ A).map e.inv).hom b
  obtain ⟨V', f, ⟨v, hv⟩, hσ⟩ := exists_map_eq_zero_openImmersionLowerShriek j M.X
    (V := ProEt.mk (𝟙 X))
    (((Sheaf.ΓNatIsoSheafSections (ProEt.topology X) A (ProEt.isTerminalMkId X)).hom.app
      ((j)_!open[A].obj M.X)).hom b') z hz
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
  -- a point of `V'` over a point of `W` specializing to `z`
  have hv' : g.base v = z := by
    have := MorphismProperty.Over.w ((ProEt.isTerminalMkId X).from V')
    rw [← hv]
    exact (congrArg (fun φ ↦ φ.base v) this).symm
  obtain ⟨v', -, hv'w⟩ := Flat.generalizingMap g (hv' ▸ hwz)
  -- a geometric point there
  let K := AlgebraicClosure (V'.left.residueField v')
  let t : Spec (.of K) ⟶ V'.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (V'.left.residueField v') K)) ≫
      V'.left.fromSpecResidueField v'
  have ht : t.base (IsLocalRing.closedPoint K) = v' := by
    simp only [t, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply v' _
  have hrange : Set.range (t ≫ g).base ⊆ Set.range (ι ≫ j).base := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨w, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht]; exact hv'w.symm⟩
  let s₀ := IsOpenImmersion.lift (ι ≫ j) (t ≫ g) hrange
  have hs₀ : s₀ ≫ ι ≫ j = t ≫ g := IsOpenImmersion.lift_fac _ _ _
  let s := s₀ ≫ ι
  have hs : s ≫ j = t ≫ g := by rw [Category.assoc]; exact hs₀
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
  -- the restriction `γ` of `b` to `Y`, and its further restriction `γW` to `W`
  let γ := (adicUpperStarUnitIso l j).inv ≫ (j)^*ᵃ[l].map β
  have hγb : globalSectionOfModHom γ = ((globalSectionsToUpperStar A j).app N).hom b :=
    (globalSectionsToUpperStar_globalSectionOfModHom j β).symm
  let γW := (adicUpperStarUnitIso l ι).inv ≫ (ι)^*ᵃ[l].map γ
  have hlisse : IsAdicLisseSheaf ((ι)^*ᵃ[l].obj ((j)^*ᵃ[l].obj ((j)_!ᵃ[l].obj M))) :=
    hH.of_iso ((asIso ((adicUpperStarLowerStarAdjunction l ι).counit.app H)).symm ≪≫
      (ι)^*ᵃ[l].mapIso (asIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M)))
  have hγW : γW = 0 := hlisse.eq_zero_of_globalSectionsToUpperStar_eq_zero_of_preconnectedSpace
    γW K s₀ (by
      have key : globalSectionOfModHom γW =
          ((globalSectionsToUpperStar A ι).app ((j)^*ᵃ[l].obj ((j)_!ᵃ[l].obj M)).X).hom
            (globalSectionOfModHom γ) :=
        (globalSectionsToUpperStar_globalSectionOfModHom ι γ).symm
      rw [key, hγb]
      have hc := congrArg (fun φ ↦ φ.hom (((globalSectionsToUpperStar A j).app N).hom b))
        (globalSectionsToUpperStar_comp A s₀ ι ((j)^*ᵃ[l].obj ((j)_!ᵃ[l].obj M)).X)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearMap.comp_apply] at hc
      erw [← hc]
      change ((Sheaf.Γ _ A).map ((upperStarComp A s₀ ι).hom.app _)).hom
        (((globalSectionsToUpperStar A s).app _).hom
          (((globalSectionsToUpperStar A j).app N).hom b)) = 0
      rw [h₄, map_zero])
  -- hence `γ = 0`, as `ι^*` is faithful on morphisms into `ι_* H`
  have hγ : γ = 0 := by
    let u := asIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M)
    have h₀ : (ι)^*ᵃ[l].map (γ ≫ u.inv) = 0 := by
      have : (ι)^*ᵃ[l].map γ = 0 := by
        have h : (ι)^*ᵃ[l].map γ = (adicUpperStarUnitIso l ι).hom ≫ γW := by
          simp only [γW, Iso.hom_inv_id_assoc]
        rw [h, hγW, comp_zero]
      rw [Functor.map_comp, this, zero_comp]
    let adj := adicUpperStarLowerStarAdjunction l ι
    have h₅ : γ ≫ u.inv = 0 := by
      apply (adj.homEquiv _ _).symm.injective
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h₀, zero_comp,
        Functor.map_zero, zero_comp]
    simpa using congrArg (· ≫ u.hom) h₅
  have h0 {P : AdicSheaf l Y} : globalSectionOfModHom (0 : AdicSheaf.unit l Y ⟶ P) = 0 := by
    rw [globalSectionOfModHom_eq]
    rw [Mod.zero_hom, Functor.map_zero]
    rfl
  have h₅ : ((globalSectionsToUpperStar A j).app N).hom b = 0 := by
    rw [← hγb, hγ, h0]
  have h₆ : b = 0 := injective_globalSectionsToUpperStar_adicOpenImmersionLowerShriek j M
    (h₅.trans (map_zero _).symm)
  have h0' : globalSectionOfModHom (0 : AdicSheaf.unit l X ⟶ (j)_!ᵃ[l].obj M) = 0 := by
    rw [globalSectionOfModHom_eq]
    rw [Mod.zero_hom, Functor.map_zero]
    rfl
  exact (bijective_globalSectionOfModHom _).1 (h₆.trans h0'.symm)

/-- **The extension by zero of a direct image of a lisse sheaf has no global section** as soon
as a point `z` outside the open `Y` is a specialization of a point of the connected noetherian
open `W ⊆ Y` carrying the lisse sheaf. -/
theorem IsAdicLisseSheaf.isZero_globalSections_adicOpenImmersionLowerShriek_adicLowerStar
    [NoetherianSpace W] [PreconnectedSpace W] {H : AdicSheaf l W} (hH : IsAdicLisseSheaf H)
    {w : W} {z : X} (hz : z ∉ Set.range j.base) (hwz : j.base (ι.base w) ⤳ z) :
    IsZero ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      ((j)_!ᵃ[l].obj ((ι)_*ᵃ[l].obj H)).X) := by
  have : Subsingleton ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      ((j)_!ᵃ[l].obj ((ι)_*ᵃ[l].obj H)).X) := by
    refine ⟨fun a c ↦ ?_⟩
    obtain ⟨α, rfl⟩ := (bijective_globalSectionOfModHom _).2 a
    obtain ⟨δ, rfl⟩ := (bijective_globalSectionOfModHom _).2 c
    rw [hH.eq_zero_of_hom_adicOpenImmersionLowerShriek_adicLowerStar j ι hz hwz α,
      hH.eq_zero_of_hom_adicOpenImmersionLowerShriek_adicLowerStar j ι hz hwz δ]
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.ProEtale
