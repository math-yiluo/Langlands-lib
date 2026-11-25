/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedCompositorCoherence
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.AlgebraicGeometry.Compactification.DenseRefinementMorphisms

/-!
# Independence of compactification and the cocycle condition

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
proposition-construction-independence-rf-shriek (blueprint:
proposition-construction-independence-rf-shriek).

The domain is the recorded ambient localizing closure. The target remains the ordinary
unbounded derived category of module objects. Comparisons are normalized by the existing
open-adjunction refinement map and the canonical derived direct-image compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

private theorem isIso_map_comp_natIso {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D) (G : E ⥤ C) (H I : E ⥤ D)
    (κ : H ≅ G ⋙ F) (τ : H ≅ I) (M : E) {A : C} (a : A ⟶ G.obj M)
    [IsIso a] : IsIso (F.map a ≫ κ.inv.app M ≫ τ.hom.app M) := by
  infer_instance

private theorem iso_square_rearrange {C : Type*} [Category C]
    {X Y Z W V : C} (a : X ≅ Y) (b : Y ⟶ Z) (c : X ≅ W)
    (d : W ≅ V) (e : V ≅ Z) (h : a.hom ≫ b = c.hom ≫ d.hom ≫ e.hom) :
    a.inv = b ≫ e.inv ≫ d.inv ≫ c.inv := by
  apply (cancel_epi a.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem adjoint_transpose_naturality {C D E : Type*}
    [Category C] [Category D] [Category E] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (F : E ⥤ C) (G : E ⥤ D) (τ : F ⟶ G ⋙ R)
    {A B : E} (a : A ⟶ B) :
    L.map (F.map a) ≫ (adj.homEquiv (F.obj B) (G.obj B)).symm (τ.app B) =
      (adj.homEquiv (F.obj A) (G.obj A)).symm (τ.app A) ≫ G.map a := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simpa only [Equiv.apply_symm_apply, Functor.comp_obj, Functor.comp_map] using τ.naturality a

private theorem component_chase {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ D) (G : B ⥤ A) (H : C ⥤ B) (P : B ⥤ D) (Q : C ⥤ D)
    (T : C ⥤ A) (α : G ⋙ F ⟶ P) (β : H ⋙ P ⟶ Q) (κ : T ⟶ H ⋙ G)
    (δ : T ⋙ F ⟶ Q) {M : A} {N : B} (L : C)
    (a : M ⟶ G.obj N) (b : N ⟶ H.obj L) (c : M ⟶ T.obj L)
    (he : c ≫ κ.app L = a ≫ G.map b)
    (ht : δ.app L = F.map (κ.app L) ≫ α.app (H.obj L) ≫ β.app L) :
    F.map c ≫ δ.app L = (F.map a ≫ α.app N) ≫ P.map b ≫ β.app L := by
  rw [ht, ← Category.assoc, ← Category.assoc, ← F.map_comp, he, F.map_comp]
  have hn := α.naturality b
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn]

private theorem comparisons_of_refinements
    {C D : Type*} [Category C] [Category D] (P : C → Prop) (F : C → D)
    (ρ : ∀ {c d : C}, (d ⟶ c) → (F c ⟶ F d))
    (hcomp : ∀ {c d e : C} (r : d ⟶ c) (s : e ⟶ d), ρ (s ≫ r) = ρ r ≫ ρ s)
    (hiso : ∀ {c d : C} (_hd : P d) (r : d ⟶ c), IsIso (ρ r))
    (hcommon : ∀ c d : C, ∃ e : C, P e ∧ Nonempty (e ⟶ c) ∧ Nonempty (e ⟶ d))
    (hthin : ∀ {d : C}, P d → ∀ c : C, Subsingleton (d ⟶ c)) :
    ∃ φ : ∀ c d : C, F c ≅ F d,
      (∀ (c₁ c₂ d : C) (_hd : P d) (h₁ : d ⟶ c₁) (h₂ : d ⟶ c₂),
        (φ c₁ c₂).hom ≫ ρ h₂ = ρ h₁) ∧
      (∀ c : C, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : C, φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) := by
  classical
  have hcommon' := hcommon
  choose e he hp hq using hcommon'
  let p (c d : C) : e c d ⟶ c := (hp c d).some
  let q (c d : C) : e c d ⟶ d := (hq c d).some
  let R {c d : C} (hd : P d) (r : d ⟶ c) : F c ≅ F d :=
    letI := hiso hd r
    asIso (ρ r)
  let φ (c d : C) : F c ≅ F d := R (he c d) (p c d) ≪≫ (R (he c d) (q c d)).symm
  have hnorm (c₁ c₂ d : C) (_hd : P d) (h₁ : d ⟶ c₁) (h₂ : d ⟶ c₂) :
      (φ c₁ c₂).hom ≫ ρ h₂ = ρ h₁ := by
    obtain ⟨w, hw, ⟨a⟩, ⟨b⟩⟩ := hcommon (e c₁ c₂) d
    have := hiso hw a
    have := hiso hw b
    have eq₁ : a ≫ p c₁ c₂ = b ≫ h₁ := (hthin hw c₁).elim _ _
    have eq₂ : a ≫ q c₁ c₂ = b ≫ h₂ := (hthin hw c₂).elim _ _
    apply (cancel_mono (ρ b)).1
    rw [Category.assoc, ← hcomp, ← hcomp, ← eq₁, ← eq₂, hcomp, hcomp]
    have := hiso (he c₁ c₂) (q c₁ c₂)
    dsimp only [φ, R, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  refine ⟨φ, hnorm, ?_, ?_⟩
  · intro c
    apply Iso.ext
    have := hiso (he c c) (p c c)
    apply (cancel_mono (ρ (p c c))).1
    simpa using hnorm c c (e c c) (he c c) (p c c) (p c c)
  · intro c₁ c₂ c₃
    obtain ⟨z, _hz, ⟨a⟩, ⟨b⟩⟩ := hcommon c₁ c₂
    obtain ⟨w, hw, ⟨k⟩, ⟨l⟩⟩ := hcommon z c₃
    have := hiso hw l
    apply Iso.ext
    apply (cancel_mono (ρ l)).1
    change ((φ c₁ c₂).hom ≫ (φ c₂ c₃).hom) ≫ ρ l = (φ c₁ c₃).hom ≫ ρ l
    rw [Category.assoc, hnorm c₂ c₃ w hw (k ≫ b) l,
      hnorm c₁ c₂ w hw (k ≫ a) (k ≫ b), hnorm c₁ c₃ w hw (k ≫ a) l]

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The already defined compactification candidate, with source restricted to Loc(Dctf).
No target preservation is assumed. Source: blueprint
proposition-construction-independence-rf-shriek, opening formula and proof step 1 (blueprint:
proposition-construction-independence-rf-shriek). -/
abbrev compactificationLocalizingCandidate {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  (localizingClosureProEtale Λ X).ι ⋙
    rightDerivedLowerShriekOfCompactification Λ c.obj.obj

/-- The component ρ_h : F_c(K) → F_d(K) for a boundary-preserving refinement h : d → c.
It is Rp_* of the canonical open-adjunction map, followed by the inverse derived
compositor and the structural triangle equality. This definition does not require either
compactification to be dense and makes no arbitrary choice of a comparison.
Source: blueprint proposition-construction-independence-rf-shriek, proof step 4
(blueprint: proposition-construction-independence-rf-shriek). -/
def compactificationRefinementComponent {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c)
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (localizingRefinementMap Λ h K) ≫
    (refinementDerivedLowerStarComp Λ h.hom.hom.hom c.obj.obj.g).inv.app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ h.hom.hom.hom_g)).hom.app
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)

section RefinementInvertibility

-- The instances and transparency of CompactificationRefinementLocalizing, for its clause (2).
attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory
attribute [local instance 2000] CategoryTheory.scalarTensor4 CategoryTheory.scalarTensor12
  CategoryTheory.scalarTensor23 CategoryTheory.scalarTensorColimits
  CategoryTheory.scalarFlipTensorColimits
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStarFromPoint
attribute [local instance 2000] CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem boundaryVanishing_of_dense
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : StandardCoefficient Λ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) :
    IsZero ((upperStar Λ c.obj.obj.i.closedComplement).mapDerivedCategory.obj
      ((lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K))) := by
  have : QuasiCompact c.obj.obj.i := c.obj.property
  have : QuasiCompact d.obj.obj.i := d.obj.property
  have : IsSchemeTheoreticallyDominant d.obj.obj.i := hd
  let cr : Compactification (𝟙 X ≫ c.obj.obj.i) :=
    { Z := d.obj.obj.Z
      i := d.obj.obj.i
      g := r.hom.hom.hom
      comm := by simpa only [Category.id_comp] using r.hom.hom.i_hom.symm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let bc : Compactification.BoundaryCompactification (𝟙 X ≫ c.obj.obj.i) :=
    ⟨⟨cr, inferInstance⟩⟩
  have : bc.obj.obj.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hcomp := properOpenInterchange Λ (𝟙 X) c.obj.obj.i bc ℓ k hΛ
  obtain ⟨m, hm, huniq, hmiso⟩ := hcomp.2 K
  have : IsIso m := hmiso (fun P hP hSP ↦ hSP K hK)
  let i := c.obj.obj.i.closedComplement
  have hdis : Disjoint (Set.range c.obj.obj.i.base) (Set.range i.base) := by
    dsimp only [i]
    rw [Scheme.Hom.range_closedComplement]
    exact disjoint_compl_right
  have hz := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
    Λ c.obj.obj.i i hdis ((lowerStar Λ (𝟙 X)).rightDerivedFunctor.obj K)
  have hz' := hz.of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm.app _)
  exact hz'.of_iso (((upperStar Λ i).mapDerivedCategory.mapIso (asIso m)).symm)

-- Clause (2) of localizingRefinement_coherence, with c not required to be dense.
-- Only the refining compactification d is used densely, in the proper/open interchange.
private theorem refinementMap_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : localizingClosureProEtale Λ X K) :
    IsIso (localizingRefinementMap Λ r K) := by
  have : QuasiCompact c.obj.obj.i := c.obj.property
  have : QuasiCompact d.obj.obj.i := d.obj.property
  let i := c.obj.obj.i.closedComplement
  let J := (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory
  let R := (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor
  let V := (upperStar Λ i).mapDerivedCategory
  let F := J ⋙ R ⋙ V
  let : F.Additive := inferInstance
  let : F.CommShift ℤ := inferInstance
  let : F.IsTriangulated := inferInstance
  let S : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
    constantModelBoundedConstructible Λ X ⊓ fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L
  have hloc := (ProEtale.localizingClosure_exists Λ X S).2.2.2.1
  let cr : Compactification c.obj.obj.i :=
    { Z := d.obj.obj.Z
      i := d.obj.obj.i
      g := r.hom.hom.hom
      comm := r.hom.hom.i_hom.symm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let bc : Compactification.BoundaryCompactification c.obj.obj.i :=
    ⟨⟨cr, inferInstance⟩⟩
  have : CompactSpace c.obj.obj.Z :=
    QuasiCompact.compactSpace_of_compactSpace (c.obj.obj.Z ↘ Spec (.of k))
  have : QuasiSeparatedSpace c.obj.obj.Z :=
    quasiSeparatedSpace_of_quasiSeparated (c.obj.obj.Z ↘ Spec (.of k))
  have hsums := (compactification_localizing Λ ℓ k c.obj.obj.i bc hΛ).2.2.1
  let adj := (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction
  let : V.IsLeftAdjoint := adj.isLeftAdjoint
  have hz : IsZero (F.obj K) := by
    apply CategoryTheory.extend_zero S hloc F _ _ K hK
    · intro I L hL
      -- the sum is indexed by the morphism universe: lift its index to the universe of `hsums`
      have : PreservesColimit L (J ⋙ R) := by
        let e := Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)
        have h' : PreservesColimit (e.functor ⋙ L) (J ⋙ R) :=
          hsums (ULift.{u + 2} I) (e.functor ⋙ L) (fun i ↦ hL (Equiv.ulift i))
        exact Functor.Final.preservesColimit_of_comp (F := e.functor)
      change PreservesColimit L ((J ⋙ R) ⋙ V)
      have : PreservesColimit (L ⋙ J ⋙ R) V :=
        adj.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
      exact comp_preservesColimit (J ⋙ R) V
    · intro L hL
      exact boundaryVanishing_of_dense Λ ℓ k (admissible_standard Λ ℓ hΛ)
        f hd r L hL
  have hij : IsCompl (Set.range i.base) (Set.range c.obj.obj.i.base) := by
    dsimp only [i]
    rw [Scheme.Hom.range_closedComplement]
    exact isCompl_compl.symm
  apply (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i
    c.obj.obj.i hij).isIso_of_pairFunctor (localizingRefinementMap Λ r K)
  · apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.i) _).2
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
    let ρ := (refinementOpenRestriction Λ r.hom.hom).app (J.obj K)
    have : IsIso ρ := by
      have := refinementOpenRestriction_isIso Λ r
      dsimp only [ρ]
      infer_instance
    have he := localizingRefinementMap_normalized Λ r K
    have : IsIso (a.unit.app K ≫
        (upperStar Λ c.obj.obj.i).mapDerivedCategory.map
          (localizingRefinementMap Λ r K) ≫ ρ) := by
      rw [he]
      infer_instance
    have : IsIso ((upperStar Λ c.obj.obj.i).mapDerivedCategory.map
        (localizingRefinementMap Λ r K) ≫ ρ) :=
      IsIso.of_isIso_comp_left (a.unit.app K) _
    exact IsIso.of_isIso_comp_right _ ρ
  · have hzsrc := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ c.obj.obj.i i hij.symm.disjoint K
    have hztgt := hz.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ i).app _)
    exact hzsrc.isIso hztgt _

end RefinementInvertibility

attribute [local irreducible] compactificationRefinementComponent localizingClosureProEtale
  DerivedCategory.monoidalClosed
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar openImmersionLowerShriek
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStarLowerStarAdjunction

private theorem refinementComponent_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification.BoundaryCompactification f}
    (hd : IsSchemeTheoreticallyDominant d.obj.obj.i) (r : d ⟶ c)
    (K : (localizingClosureProEtale Λ X).FullSubcategory) :
    IsIso (compactificationRefinementComponent Λ r K.obj) := by
  have := refinementMap_isIso Λ ℓ hΛ k hd r K.obj K.property
  unfold compactificationRefinementComponent
  exact isIso_map_comp_natIso (lowerStar Λ c.obj.obj.g).rightDerivedFunctor
    (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor
    (lowerStar Λ (r.hom.hom.hom ≫ c.obj.obj.g)).rightDerivedFunctor
    (lowerStar Λ d.obj.obj.g).rightDerivedFunctor
    (refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g)
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ r.hom.hom.hom_g))
    ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K.obj)
    (localizingRefinementMap Λ r K.obj)

omit [IsCommMonObj Λ] in
private theorem derive_eqToIso {A B : Scheme.{u}} {g h : A ⟶ B} (w : g = h) :
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ w)).hom =
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor) w)).hom := by
  cases w
  simp [lowerStarCongr, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans]

private theorem compositor_transport
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {A B C D : Scheme.{u}} (k : A ⟶ B) (h : B ⟶ C) (g : C ⟶ D)
    (p : B ⟶ D) (q : A ⟶ D) (hp : h ≫ g = p) (hq : k ≫ p = q)
    (hr : (k ≫ h) ≫ g = q)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A))) :
    (refinementDerivedLowerStarComp Λ (k ≫ h) g).inv.app M ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ hr)).hom.app M =
      (lowerStar Λ g).rightDerivedFunctor.map
          ((refinementDerivedLowerStarComp Λ k h).hom.app M) ≫
        (refinementDerivedLowerStarComp Λ h g).inv.app
          ((lowerStar Λ k).rightDerivedFunctor.obj M) ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ hp)).hom.app
          ((lowerStar Λ k).rightDerivedFunctor.obj M) ≫
        (refinementDerivedLowerStarComp Λ k p).inv.app M ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ hq)).hom.app M := by
  simp only [derive_eqToIso]
  subst p
  subst q
  have hκ : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      refinementDerivedLowerStarComp Λ a b = moduleDerivedCompositor Λ a b := by
    intro A B C a b
    unfold refinementDerivedLowerStarComp moduleDerivedCompositor
      Functor.rightDerivedFunctorCompIso' Functor.rightDerivedFunctorNatIso
    rfl
  simp only [hκ, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Category.id_comp]
  have hc := congrArg (fun e ↦ e.hom.app M)
    (module_derived_compositor_coherence Λ ℓ hΛ k h g)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, derive_eqToIso] at hc
  exact iso_square_rearrange
    ((moduleDerivedCompositor Λ (k ≫ h) g).app M)
    ((lowerStar Λ g).rightDerivedFunctor.map ((moduleDerivedCompositor Λ k h).hom.app M))
    ((eqToIso (congrArg (fun t ↦ (lowerStar Λ t).rightDerivedFunctor)
      (Category.assoc k h g))).app M)
    ((moduleDerivedCompositor Λ k (h ≫ g)).app M)
    ((moduleDerivedCompositor Λ h g).app ((lowerStar Λ k).rightDerivedFunctor.obj M)) hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem refinementComponent_comp
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification.BoundaryCompactification f} (r : d ⟶ c) (s : e ⟶ d)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    compactificationRefinementComponent Λ (s ≫ r) K =
      compactificationRefinementComponent Λ r K ≫ compactificationRefinementComponent Λ s K := by
  let J := (openImmersionLowerShriek Λ e.obj.obj.i).mapDerivedCategory.obj K
  let α := (refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g).inv ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ r.hom.hom.hom_g)).hom
  let β := (refinementDerivedLowerStarComp Λ s.hom.hom.hom d.obj.obj.g).inv ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ s.hom.hom.hom_g)).hom
  let δ := (refinementDerivedLowerStarComp Λ (s.hom.hom.hom ≫ r.hom.hom.hom)
    c.obj.obj.g).inv ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ (s ≫ r).hom.hom.hom_g)).hom
  have ht := compositor_transport Λ ℓ hΛ s.hom.hom.hom r.hom.hom.hom c.obj.obj.g
    d.obj.obj.g e.obj.obj.g r.hom.hom.hom_g s.hom.hom.hom_g (s ≫ r).hom.hom.hom_g J
  have h := component_chase (lowerStar Λ c.obj.obj.g).rightDerivedFunctor
    (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor
    (lowerStar Λ s.hom.hom.hom).rightDerivedFunctor
    (lowerStar Λ d.obj.obj.g).rightDerivedFunctor
    (lowerStar Λ e.obj.obj.g).rightDerivedFunctor
    (lowerStar Λ (s.hom.hom.hom ≫ r.hom.hom.hom)).rightDerivedFunctor α β
    (refinementDerivedLowerStarComp Λ s.hom.hom.hom r.hom.hom.hom).hom δ J
    (localizingRefinementMap Λ r K) (localizingRefinementMap Λ s K)
    (localizingRefinementMap Λ (s ≫ r) K)
    (localizingRefinementMap_comp Λ r s K) (by
      simpa only [δ, α, β, NatTrans.comp_app, Category.assoc] using ht)
  dsimp only [α, β, δ, J, NatTrans.comp_app] at h
  convert h using 1 <;> unfold compactificationRefinementComponent <;> rfl

private theorem refinementMap_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))} (a : K ⟶ L) :
    (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.map a ≫
        localizingRefinementMap Λ r L = localizingRefinementMap Λ r K ≫
      (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.map
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.map a) := by
  let := refinementOpenRestriction_isIso Λ r
  let t : (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory ⋙
      (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor ⋙
      (upperStar Λ c.obj.obj.i).mapDerivedCategory ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft _ (asIso (refinementOpenRestriction Λ r.hom.hom)) ≪≫
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit).symm
  have h := adjoint_transpose_naturality
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (𝟭 _) ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory ⋙
      (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor) t.inv a
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_map, Functor.comp_obj,
    localizingRefinementMap, t, refinementTheta, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    NatIso.isIso_inv_app, asIso_inv, asIso_hom] using h

private theorem refinementComponent_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    {K L : (localizingClosureProEtale Λ X).FullSubcategory} (a : K ⟶ L) :
    (compactificationLocalizingCandidate Λ c).map a ≫
        compactificationRefinementComponent Λ r L.obj =
      compactificationRefinementComponent Λ r K.obj ≫
        (compactificationLocalizingCandidate Λ d).map a := by
  let η : (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory ⋙
        (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor :=
    { app := fun K ↦ localizingRefinementMap Λ r K
      naturality := fun _ _ a ↦ refinementMap_naturality Λ r a }
  let τ := Functor.whiskerRight η (lowerStar Λ c.obj.obj.g).rightDerivedFunctor ≫
    (Functor.associator (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory
      (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor
      (lowerStar Λ c.obj.obj.g).rightDerivedFunctor).hom ≫
    Functor.whiskerLeft (openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory
      ((refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g).inv ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ r.hom.hom.hom_g)).hom)
  simpa only [τ, η, compactificationRefinementComponent, compactificationLocalizingCandidate,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, ObjectProperty.ι_obj, ObjectProperty.ι_map] using τ.naturality a.hom

/-- Canonical natural comparisons between all compactifications, independent of the common
scheme-theoretically dense refinement, with identity normalization and the cocycle law.
The first clause records that the refinement components used in the formula really are
isomorphisms; the next clause is φ_{c₂,c₁} ρ_{h₂} = ρ_{h₁}, equivalently
φ_{c₂,c₁} = ρ_{h₁} ρ_{h₂}⁻¹, for every common dense refinement and both its projections.
The last two clauses are equalities of natural isomorphisms, not just objectwise existence.
Source: blueprint main-20261015, proposition-construction-independence-rf-shriek
(blueprint: proposition-construction-independence-rf-shriek).

Proof, following the seven DAG steps:
1. Work with F_c = Rp_* D(j_!) on ordinary unbounded module-object derived categories,
restricting only the source to Loc(Dctf). The canonical derived composition comparison
is normalized on K-injective complexes by the underived module compositor. Exact
coefficient pullback makes direct image preserve K-injectives, so all parenthesizations
use the same complex. The underived fibre-product identifications give associativity.
2. For h : d → c with d dense, apply proper/open interchange at p = id_X and i = j_c,
with dense compactification (j_d,h). Its unique identity-on-restriction arrow is the
existing localizingRefinementMap, by the exact open derived adjunction. It is invertible
on Loc(Dctf), naturally in K, even when c is not dense.
3. Over V → X, the boundary equality identifies V ×_{Z_c} Z_d with V, with the same
coefficient action. Exact restriction and preservation of K-injectives by the right
adjoint of exact j_d! give j_c* Rh* ≅ j_d*. These identifications commute with composition.
4. Apply Rp_* to the arrow in step 2 and invert the derived compositor, giving exactly
compactificationRefinementComponent. For a further dense refinement, both open arrows
restrict to the identity; uniqueness from interchange makes them equal. Naturality and
associativity of the compositor give ρ_hk = ρ_h ρ_k. Identity follows the same way.
5. Choose a common dense refinement using
proposition-dense-compactifications-form-cofiltered-category--1. Define φ_{c₂,c₁} = ρ_{h₁} ρ_{h₂}⁻¹.
The two arrows are invertible by step 4, and naturality gives an isomorphism of the restricted
functors with ambient target.
6. Dominate two chosen common dense refinements by another dense refinement. Schematic
density of its source and separatedness of each proper target give equality of the two
composites to each c_a, by proposition-dense-compactifications-form-cofiltered-category--2 (3). Step
4 and cancellation of the intervening isomorphisms prove the normalization for every common
refinement.
7. Dominate three compactifications simultaneously using the finite-family conclusion
of common dense refinement. Independence allows all three comparisons to be computed
there, and the middle factors cancel, proving the cocycle. For φ_{c,c} use the same
projection twice; this proves identity even for a nondense c. -/
theorem compactification_coherence_cocycle
    (ℓ : ℕ) [Fact ℓ.Prime] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ φ : ∀ c₁ c₂ : Compactification.BoundaryCompactification f,
        compactificationLocalizingCandidate Λ c₁ ≅ compactificationLocalizingCandidate Λ c₂,
      (∀ (c : Compactification.BoundaryCompactification f)
        (d : Compactification.DenseBoundaryCompactification f) (h : d.obj ⟶ c)
        (K : (localizingClosureProEtale Λ X).FullSubcategory),
        IsIso (compactificationRefinementComponent Λ h K.obj)) ∧
      (∀ (c₁ c₂ : Compactification.BoundaryCompactification f)
        (d : Compactification.DenseBoundaryCompactification f)
        (h₁ : d.obj ⟶ c₁) (h₂ : d.obj ⟶ c₂)
        (K : (localizingClosureProEtale Λ X).FullSubcategory),
        (φ c₁ c₂).hom.app K ≫ compactificationRefinementComponent Λ h₂ K.obj =
          compactificationRefinementComponent Λ h₁ K.obj) ∧
      (∀ c : Compactification.BoundaryCompactification f, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification.BoundaryCompactification f,
        φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) := by
  classical
  let P (c : Compactification.BoundaryCompactification f) : Prop :=
    IsSchemeTheoreticallyDominant c.obj.obj.i
  let F (c : Compactification.BoundaryCompactification f) :=
    compactificationLocalizingCandidate Λ c
  let ρ {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) : F c ⟶ F d :=
    { app := fun K ↦ compactificationRefinementComponent Λ r K.obj
      naturality := fun _ _ a ↦ refinementComponent_naturality Λ r a }
  have hcomp {c d e : Compactification.BoundaryCompactification f} (r : d ⟶ c) (s : e ⟶ d) :
      ρ (s ≫ r) = ρ r ≫ ρ s := by
    ext K
    exact refinementComponent_comp Λ ℓ _hΛ r s K.obj
  have hiso {c d : Compactification.BoundaryCompactification f} (_hd : P d) (r : d ⟶ c) :
      IsIso (ρ r) := by
    have : ∀ K, IsIso ((ρ r).app K) := fun K ↦ refinementComponent_isIso Λ ℓ _hΛ k _hd r K
    exact NatIso.isIso_of_isIso_app _
  have hcommon (c d : Compactification.BoundaryCompactification f) :
      ∃ e : Compactification.BoundaryCompactification f,
        P e ∧ Nonempty (e ⟶ c) ∧ Nonempty (e ⟶ d) := by
    rcases Compactification.exists_common_dense_refinement.{u, u} f c.obj.obj d.obj.obj with
      ⟨_, _, hqc, hd, _, _, _, _, _, _, _, h₁, h₂, _⟩
    let e : Compactification.BoundaryCompactification f :=
      ⟨⟨Compactification.inf c.obj.obj d.obj.obj, hqc⟩⟩
    refine ⟨e, hd, ⟨?_⟩, ⟨?_⟩⟩
    · exact ⟨ObjectProperty.homMk (Compactification.infFst c.obj.obj d.obj.obj), h₁⟩
    · exact ⟨ObjectProperty.homMk (Compactification.infSnd c.obj.obj d.obj.obj), h₂⟩
  have hthin {d : Compactification.BoundaryCompactification f} (hd : P d)
      (c : Compactification.BoundaryCompactification f) : Subsingleton (d ⟶ c) := by
    constructor
    intro a b
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Compactification.Refinement.ext
    exact ((denseCompactification_refinement_morphisms d.obj c.obj hd
      a.hom.hom.hom a.hom.hom.hom_g a.hom.hom.i_hom).2.2
        b.hom.hom.hom b.hom.hom.hom_g b.hom.hom.i_hom).symm
  obtain ⟨φ, hn, hi, hc⟩ := comparisons_of_refinements P F ρ hcomp hiso hcommon hthin
  refine ⟨φ, ?_, ?_, hi, hc⟩
  · intro c d r K
    exact refinementComponent_isIso Λ ℓ _hΛ k d.property r K
  · intro c₁ c₂ d h₁ h₂ K
    exact congrArg (fun t ↦ t.app K) (hn c₁ c₂ d.obj d.property h₁ h₂)

end AlgebraicGeometry.ProEtale.CondensedRing
