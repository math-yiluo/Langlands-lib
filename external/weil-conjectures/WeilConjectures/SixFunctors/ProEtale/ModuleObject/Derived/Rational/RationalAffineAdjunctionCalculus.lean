/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AffineSpaceRationalLine
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekComposition
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Restricting and composing rational compact-support adjunctions

Source: blueprint affine-space induction, the identity and composition arguments
(blueprint: lem-sfb-rational-affine-adjunction-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A specified ambient functor is the right adjoint of the specified compactification
image on the literal rational localizing categories. Source: blueprint induction, Step 5
(blueprint: lem-sfb-rational-affine-adjunction-calculus). -/
def RationalCompactSupportAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (H : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) : Prop :=
  ∃ (F : rationalLocalizingCategory Λ X ⥤ rationalLocalizingCategory Λ Y)
    (P : rationalLocalizingCategory Λ Y ⥤ rationalLocalizingCategory Λ X),
    Nonempty (F ⋙ rationalLocalizingInclusion Λ Y ≅
      rationalLocalizingInclusion Λ X ⋙ rightDerivedLowerShriekOfCompactification Λ c) ∧
    Nonempty (P ⋙ rationalLocalizingInclusion Λ X ≅ rationalLocalizingInclusion Λ Y ⋙ H) ∧
    Nonempty (F ⊣ P)

private theorem rationalClosureEq
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    localizingClosureProEtale (RationalP1.coefficient ℓ c).X X =
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (RationalP1.coefficient ℓ c).X X) := by
  apply (localizingClosure_ctf_equals_bc ℓ X (RationalP1.coefficient ℓ c).X ?_).1.2.2.2.1
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  | some E => exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))

private theorem rationalAdmissible
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ)) :
    IsLocalizingAdmissibleCoefficient ℓ (RationalP1.coefficient.{u} ℓ c).X := by
  cases c with
  | none => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  | some E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))

/-- Replacing the displayed ambient right adjoint by an isomorphic functor does not
change its restricted adjunction. Source: blueprint induction, functor comparisons
(blueprint: lem-sfb-rational-affine-adjunction-calculus). -/
theorem RationalCompactSupportAdjunction.ofIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f}
    {H H' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))}
    (h : RationalCompactSupportAdjunction Λ c H) (e : H ≅ H') :
    RationalCompactSupportAdjunction Λ c H' := by
  obtain ⟨F, P, hF, ⟨hP⟩, adj⟩ := h
  exact ⟨F, P, hF, ⟨hP ≪≫ Functor.isoWhiskerLeft _ e⟩, adj⟩

/-- Open restriction, for any chosen compactification, is the exceptional inverse image
on Loc(Dbc). Source: blueprint induction, Steps 4 and 6
(blueprint: lem-sfb-rational-affine-adjunction-calculus).
Proof: replace Loc(Dbc) by Loc(Dctf) using their equality for rational coefficients.
Restrict the exact open adjunction. The trivial compactification computes extension
by zero; compactification coherence compares it with the given one. -/
theorem rationalOpenCompactSupportAdjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (b : Compactification j) :
    RationalCompactSupportAdjunction (RationalP1.coefficient ℓ c).X b
      (upperStar (RationalP1.coefficient ℓ c).X j).leftDerivedFunctor := by
  let Λ := (RationalP1.coefficient ℓ c).X
  let : U.Over (Spec (.of k)) := ⟨j ≫ (X ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ (X ↘ Spec (.of k))))
  have : QuasiCompact (U ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (j ≫ (X ↘ Spec (.of k))))
  have : IsSeparated (U ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (j ≫ (X ↘ Spec (.of k))))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated (U ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have hU := rationalClosureEq ℓ c U
  have hX := rationalClosureEq ℓ c X
  unfold RationalCompactSupportAdjunction rationalLocalizingCategory rationalLocalizingInclusion
  rw [← hU, ← hX]
  obtain ⟨he, hs, ht, adj, _⟩ := mateOpenImmersion Λ ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ)
    (rationalAdmissible ℓ c) j
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ ℓ (rationalAdmissible ℓ c) k j
  let b₀ : Compactification.BoundaryCompactification j :=
    ⟨⟨Compactification.ofIsOpenImmersion j, show QuasiCompact j from inferInstance⟩⟩
  let b₁ : Compactification.BoundaryCompactification j :=
    ⟨⟨b, b.quasiCompact_openImmersion inferInstance⟩⟩
  refine ⟨mateOpenExtension Λ j he, mateOpenPullback Λ j hs, ⟨?_⟩, ⟨?_⟩, ⟨adj⟩⟩
  · exact Functor.isoWhiskerLeft (localizingClosureProEtale Λ U).ι
      (mateOpenTrivialLowerShriek Λ j).symm ≪≫ φ b₀ b₁
  · exact Functor.isoWhiskerLeft (localizingClosureProEtale Λ X).ι
      (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

-- Keep compactification and full-subcategory transports folded.
/-- Compact-support adjunctions compose with the ambient right adjoints in reverse order.
Source: blueprint induction, Step 5
(blueprint: lem-sfb-rational-affine-adjunction-calculus).
Proof: convert rational closures to the finite-Tor closures, apply the existing
compactification compositor, and compose the two adjunctions. Full faithfulness of the
inclusions identifies the supplied restrictions with those used by the compositor. -/
theorem rationalCompactSupportAdjunction_comp
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (bf : Compactification f) (bg : Compactification g)
    (bfg : Compactification (f ≫ g))
    (Hf : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (RationalP1.coefficient ℓ c).X Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (RationalP1.coefficient ℓ c).X X)))
    (Hg : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (RationalP1.coefficient ℓ c).X Z)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (RationalP1.coefficient ℓ c).X Y)))
    (hf : RationalCompactSupportAdjunction (RationalP1.coefficient ℓ c).X bf Hf)
    (hg : RationalCompactSupportAdjunction (RationalP1.coefficient ℓ c).X bg Hg) :
    RationalCompactSupportAdjunction (RationalP1.coefficient ℓ c).X bfg (Hg ⋙ Hf) := by
  let Λ := (RationalP1.coefficient ℓ c).X
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  have hX := rationalClosureEq ℓ c X
  obtain ⟨Ff, Pf, ⟨eFf⟩, ⟨ePf⟩, ⟨af⟩⟩ := hf
  obtain ⟨Fg, Pg, ⟨eFg⟩, ⟨ePg⟩, ⟨ag⟩⟩ := hg
  let E : PadicAlgCl.FiniteIntermediateField ℓ := c.getD (Classical.arbitrary _)
  have hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    cases c with
    | none => exact Or.inr ⟨Iso.refl _⟩
    | some E => exact Or.inl ⟨Iso.refl _⟩
  obtain ⟨hf', hg', hfg', α, _⟩ :=
    exists_localizingLowerShriekComposition Λ ℓ E hΛ k f g
  let cf : Compactification.BoundaryCompactification f :=
    ⟨⟨bf, bf.quasiCompact_openImmersion inferInstance⟩⟩
  let cg : Compactification.BoundaryCompactification g :=
    ⟨⟨bg, bg.quasiCompact_openImmersion inferInstance⟩⟩
  let cfg : Compactification.BoundaryCompactification (f ≫ g) :=
    ⟨⟨bfg, bfg.quasiCompact_openImmersion inferInstance⟩⟩
  have a : rationalLocalizingInclusion Λ X ⋙
        rightDerivedLowerShriekOfCompactification Λ bf ⋙
        rightDerivedLowerShriekOfCompactification Λ bg ≅
      rationalLocalizingInclusion Λ X ⋙
        rightDerivedLowerShriekOfCompactification Λ bfg := by
    let J : rationalLocalizingCategory Λ X ⥤
        (localizingClosureProEtale Λ X).FullSubcategory :=
      (localizingClosureProEtale Λ X).lift (rationalLocalizingInclusion Λ X)
        (fun K ↦ hX.symm ▸ K.property)
    exact Functor.isoWhiskerLeft J
      (Functor.isoWhiskerRight (α cf cg cfg) (localizingClosureProEtale Λ Z).ι)
  refine ⟨Ff ⋙ Fg, Pg ⋙ Pf, ⟨?_⟩, ⟨?_⟩, ⟨af.comp ag⟩⟩
  · exact Functor.isoWhiskerLeft Ff eFg ≪≫
      Functor.isoWhiskerRight eFf (rightDerivedLowerShriekOfCompactification Λ bg) ≪≫ a
  · exact Functor.isoWhiskerLeft Pg ePf ≪≫ Functor.isoWhiskerRight ePg Hf

end AlgebraicGeometry.ProEtale.CondensedRing
