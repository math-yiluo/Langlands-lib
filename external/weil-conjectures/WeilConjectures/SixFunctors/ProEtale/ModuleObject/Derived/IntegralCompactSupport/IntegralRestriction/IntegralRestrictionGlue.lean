/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestriction.IntegralRestrictionBoundedDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestriction.IntegralRestrictionCohomologyDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestriction.IntegralRestrictionChartCover

/-!
# Finite-open gluing and restriction of the integral Brown adjunction

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
sk-thm-int-restriction-glue.md (blueprint: theorem-f-shriek-ell-adic-coefficients).

The bounded constructible category uses finite constant scalar models. The restricted
adjunction has exactly the Hom equivalences of the given integral Brown adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The literal full inclusion Dbc into its ordinary localizing closure.
Source: blueprint sk-thm-int-restriction-glue, clause 2, final sentence
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
def constructibleInclusion (X : Scheme.{u}) :
    (generators Λ X).FullSubcategory ⥤ (localizing Λ X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- Restriction of the actual compactification composite Rp_* D(j_!) to Dbc,
using its asserted preservation of Dbc, without changing any morphism.
Source: blueprint sk-thm-int-restriction-glue, clause 2, final sentence
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
def restrictedLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ K, generators Λ X K → generators Λ Y ((image Λ c).obj K)) :
    (generators Λ X).FullSubcategory ⥤ (generators Λ Y).FullSubcategory :=
  (generators Λ Y).lift ((generators Λ X).ι ⋙ image Λ c)
    (fun K ↦ hF K.obj K.property)

/-- Restriction of the given Brown right adjoint to Dbc using its asserted preservation.
Source: blueprint sk-thm-int-restriction-glue, clause 2
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
def restrictedUpperShriek {X Y : Scheme.{u}}
    (G : (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory)
    (hG : ∀ K : (localizing Λ Y).FullSubcategory,
      generators Λ Y K.obj → generators Λ X (G.obj K).obj) :
    (generators Λ Y).FullSubcategory ⥤ (generators Λ X).FullSubcategory :=
  (generators Λ X).lift (constructibleInclusion Λ Y ⋙ G ⋙ (localizing Λ X).ι)
    (fun K ↦ hG ((constructibleInclusion Λ Y).obj K) K.property)

private theorem restrictAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (h : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c).obj K))
    (G : (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory)
    (adj : lowerShriek Λ c h ⊣ G)
    (hF : ∀ K, generators Λ X K → generators Λ Y ((image Λ c).obj K))
    (hG : ∀ K : (localizing Λ Y).FullSubcategory,
      generators Λ Y K.obj → generators Λ X (G.obj K).obj) :
    ∃ adj' : restrictedLowerShriek Λ c hF ⊣ restrictedUpperShriek Λ G hG,
      ∀ (A : (generators Λ X).FullSubcategory) (B : (generators Λ Y).FullSubcategory)
        (m : (restrictedLowerShriek Λ c hF).obj A ⟶ B),
        (adj'.homEquiv A B m).hom =
          (adj.homEquiv ((constructibleInclusion Λ X).obj A)
            ((constructibleInclusion Λ Y).obj B) (ObjectProperty.homMk m.hom)).hom := by
  let iX := constructibleInclusion Λ X
  let iY := constructibleInclusion Λ Y
  let comm1 : iX ⋙ lowerShriek Λ c h ≅ restrictedLowerShriek Λ c hF ⋙ iY :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let comm2 : iY ⋙ G ≅ restrictedUpperShriek Λ G hG ⋙ iX :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let adj' := adj.restrictFullyFaithful (ObjectProperty.fullyFaithfulιOfLE _)
    (ObjectProperty.fullyFaithfulιOfLE _) comm1 comm2
  refine ⟨adj', ?_⟩
  intro A B m
  simp [adj', Adjunction.restrictFullyFaithful, comm1, comm2, iX, iY,
    constructibleInclusion, ObjectProperty.fullyFaithfulιOfLE]

private theorem finiteOpenGlue (X : Scheme.{u}) [IsNoetherian X]
    (I : Type w) [Finite I] (U : I → X.Opens) (hcover : iSup U = ⊤)
    (M : Ambient Λ X)
    (hM : ∀ i : I, generators Λ (U i).toScheme ((pull Λ (U i).ι).obj M)) :
    generators Λ X M := by
  exact ⟨bounded_finiteOpenDescent Λ X I U hcover M (fun i ↦ (hM i).1),
    cohomology_finiteOpenDescent Λ X I U hcover M hM⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction
