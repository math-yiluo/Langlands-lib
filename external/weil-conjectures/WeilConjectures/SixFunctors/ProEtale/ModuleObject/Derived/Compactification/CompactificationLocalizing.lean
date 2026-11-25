/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence

/-!
# Compact support along a single compactification on the localizing category

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
proposition-construction-independence-rf-shriek and its three-paragraph proof
(blueprint: proposition-construction-independence-rf-shriek).

Restriction to the full localizing subcategories is expressed using their object predicates.
Exactness means preservation of their ambient distinguished triangles, with the canonical
composite shift comparison. Coproduct preservation means preservation of each ambient discrete
colimit whose vertices belong to the source closure, using the same indexing universe as
`localizingClosureProEtale`. These are precisely the triangles and sums of the full closures.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The compactification composite is triangulated on the ambient derived categories. -/
private theorem compactification_isTriangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (rightDerivedLowerShriekOfCompactification Λ c).IsTriangulated := by
  change ((openImmersionLowerShriek Λ c.i).mapDerivedCategory ⋙
    (lowerStar Λ c.g).rightDerivedFunctor).IsTriangulated
  infer_instance

/-- The restricted-sum criterion gives objectwise preservation of the localizing closure. -/
private theorem properImage_localizing_of_hypotheses
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ProperLocalizingHypotheses Λ p) :
    ∀ K, localizingClosureProEtale Λ X K →
      localizingClosureProEtale Λ Y ((lowerStar Λ p).rightDerivedFunctor.obj K) := by
  let P := localizingClosureProEtale Λ X
  let Q := localizingClosureProEtale Λ Y
  let F := (lowerStar Λ p).rightDerivedFunctor
  have hP : IsLocalizingSubcategory P :=
    (localizingClosure_exists Λ X
      (constantModelBoundedConstructible Λ X ⊓ fun K ↦
        DerivedCategory.finiteTorAmplitude _ K)).2.2.2.1
  have hQ : IsLocalizingSubcategory Q :=
    (localizingClosure_exists Λ Y
      (constantModelBoundedConstructible Λ Y ⊓ fun K ↦
        DerivedCategory.finiteTorAmplitude _ K)).2.2.2.1
  let := hP.1
  let := hQ.1
  let := hP.2.1
  let := hQ.2.1
  let R := P ⊓ Q.inverseImage F
  have hR : IsLocalizingSubcategory R := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I D hD hDR
    let := hD
    refine ⟨hP.2.2 D hD (fun i ↦ (hDR i).1), ?_⟩
    let L := P.lift D (fun i ↦ (hDR i.as).1)
    have : PreservesColimit (L ⋙ P.ι) F := preservesColimit_of_properLocalizingHypotheses Λ p h I L
    have : PreservesColimit D F :=
      preservesColimit_of_iso_diagram F (P.liftCompιIso D (fun i ↦ (hDR i.as).1))
    exact Q.prop_of_iso (preservesColimitIso F D).symm
      (hQ.2.2 (D ⋙ F) inferInstance (fun i ↦ (hDR i).2))
  have hgen : ∀ K, (constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K) → R K := by
    intro K hK
    refine ⟨?_, ?_⟩
    · exact fun S _ hS ↦ hS K hK
    · have hg := h.1 ⟨K, hK⟩
      exact fun S _ hS ↦ hS (F.obj K) hg
  intro K hK
  exact (hK R hR hgen).2

/-- For each specified compactification, `Rp_*` after exact extension by zero restricts
exactly to the localizing closures, preserves their direct sums, and preserves Dctf.
The four conjuncts express restriction, exactness, sums, and preservation of Dctf.
All categories are the ordinary unbounded derived categories of internal module objects.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
proposition-construction-independence-rf-shriek, statement and proof
(blueprint: proposition-construction-independence-rf-shriek).

Proof plan:
1. Apply proposition-proper-direct-image-extension-zero to the quasi-compact open immersion c.i.
Extension by zero preserves Dctf, all direct sums, and distinguished triangles; its
restriction maps the source localizing closure into the middle localizing closure.
2. Apply det-sf-comp-proper-admissible-hypotheses to the proper map c.g. Its proved
coefficient-isomorphism transport uses proposition-proper-direct-image-extension-zero--1 for the
six representatives, including the finite-subextension-valued algebraic closure.
The full continuous algebraic-closure case uses its separate proper-image theorem.
Coefficient isomorphisms are transported by exact module equivalences. These hypotheses
preserve Dctf and ambient sums on the middle closure. Intersect that closure with the inverse
image of the target closure; the restricted sum hypothesis makes the intersection
localizing. Minimality then gives objectwise preservation of the closure.
3. Compose the two restricted functors. The middle closure is the same in both steps.
Each distinguished triangle is sent to a distinguished triangle twice, with the
composite shift comparison. The two coproduct comparisons compose to the comparison
for Rp_* j_!. A Dctf object first stays Dctf under j_! and then under Rp_*.
These arguments include the empty family and the zero complex. -/
theorem compactification_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
        localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      T ∈ distTriang _ → localizingClosureProEtale Λ X T.obj₁ →
        localizingClosureProEtale Λ X T.obj₂ → localizingClosureProEtale Λ X T.obj₃ →
        (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).mapTriangle.obj T ∈
          distTriang _) ∧
    (∀ (I : Type (u + 2)) (K : Discrete I ⥤ DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      (∀ i : I, localizingClosureProEtale Λ X (K.obj (Discrete.mk i))) →
        PreservesColimit K (rightDerivedLowerShriekOfCompactification Λ c.obj.obj)) ∧
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K) ∧
          DerivedCategory.finiteTorAmplitude _
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) := by
  let c₀ := c.obj.obj
  let : c₀.Z.Over (Spec (.of k)) := ⟨c₀.g ≫ (Y ↘ Spec (.of k))⟩
  have : c₀.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : c₀.i.IsOver (Spec (.of k)) := ⟨by
    change c₀.i ≫ c₀.g ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)
    rw [← Category.assoc, ← c₀.comm]
    exact comp_over f (Spec (.of k))⟩
  have : IsSeparated (c₀.Z ↘ Spec (.of k)) := by
    change IsSeparated (c₀.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : LocallyOfFiniteType (c₀.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (c₀.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (c₀.Z ↘ Spec (.of k)) := by
    change QuasiCompact (c₀.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have hopen := openImmersionLowerShriek_localizing ℓ k (ringChar k)
    (Nat.Prime.pos Fact.out) (Fact.out : ringChar k ≠ ℓ) Λ _hΛ c₀.i
  have hproper := properLocalizingHypotheses_admissible ℓ Λ _hΛ k c₀.g
  obtain ⟨_, _, hi, _, _⟩ := hopen.2.2
  have hg := properImage_localizing_of_hypotheses Λ c₀.g hproper
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact hg _ (hi ⟨K, hK⟩)
  · intro T hT _ _ _
    have := compactification_isTriangulated Λ c₀
    exact Functor.map_distinguished _ T hT
  · intro I K hK
    let F := (openImmersionLowerShriek Λ c₀.i).mapDerivedCategory
    let G := (lowerStar Λ c₀.g).rightDerivedFunctor
    let L : Discrete I ⥤ (localizingClosureProEtale Λ c₀.Z).FullSubcategory :=
      (localizingClosureProEtale Λ c₀.Z).lift (K ⋙ F)
        (fun i ↦ hi ⟨K.obj i, hK i.as⟩)
    have : PreservesColimit (L ⋙ (localizingClosureProEtale Λ c₀.Z).ι) G :=
      hproper.2 I L
    have : PreservesColimit (K ⋙ F) G :=
      preservesColimit_of_iso_diagram G
        ((localizingClosureProEtale Λ c₀.Z).liftCompιIso (K ⋙ F)
          (fun i ↦ hi ⟨K.obj i, hK i.as⟩))
    have : PreservesColimit K F :=
      (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape
        |>.preservesColimit
    exact comp_preservesColimit F G
  · intro K hK
    exact hproper.1 ⟨_, hopen.1 ⟨K, hK⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
