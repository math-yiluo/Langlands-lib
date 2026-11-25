/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedCoefficientModel
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Constant scalar actions for the actual pulled-back coefficients

All actions are defined by constant continuous functions, followed by inverse image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.NormalizedScalar

/-- The actual inverse image from the point is additive.
Source: it is a composite of two left adjoints.
(blueprint: lem-weil-pbc-normalized-scalar-actions). -/
theorem pullback_additive (T : Scheme.{u}) : (upperStarFromPoint T).Additive := by
  have adj : upperStarFromPoint T ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
  have : (upperStarFromPoint T).IsLeftAdjoint := adj.isLeftAdjoint
  have := CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (upperStarFromPoint T)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint T) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint T)
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint T)

attribute [local instance] pullback_additive

variable (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Constant continuous functions in the original coefficient universe.
Source: Bhatt--Scholze's condensed coefficient convention.
(blueprint: lem-weil-pbc-normalized-scalar-actions). -/
def constantSections (S : Profinite.{u}ᵒᵖ) :
    B →+* (Profinite.continuousCoefficientRingSheaf B).obj.obj S where
  toFun b := ULift.up (ContinuousMap.const _ b)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The constant global sections of the condensed coefficient ring.
Source: the constant-function map into continuous coefficients.
(blueprint: lem-weil-pbc-normalized-scalar-actions). -/
def pointConstants : B →+* Γ (Profinite.continuousCoefficientRingObj B) :=
  Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u})
    (Profinite.continuousCoefficientRingSheaf B) (constantSections B) fun _ _ ↦ rfl

/-- The constant sections after the specified inverse image from the point.
Source: the pulled-back coefficient convention.
(blueprint: lem-weil-pbc-normalized-scalar-actions). -/
def constants (T : Scheme.{u}) :
    B →+* Γ (condensedRingObj (Profinite.continuousCoefficientRingObj B) T) :=
  (Γ.mapFunctor (upperStarFromPoint T)).comp (pointConstants B)

/-- Modules are linear through these actual constant sections.
Source: the action of global sections on internal modules.
(blueprint: lem-weil-pbc-normalized-scalar-actions). -/
@[instance_reducible] def modulesLinear (T : Scheme.{u}) :
    Linear B (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj B) T)) :=
  Mod.linearOfRingHom (constants B T)

variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E] [NormedAlgebra ℚ_[l] E]

/-- The actual inclusion takes each constant integral scalar to the same field scalar.
Source: functoriality of constant sections.
(blueprint: lem-weil-pbc-normalized-scalar-actions).
Proof: the sectionwise map is postcomposition with the inclusion. Naturality of
sheafification and inverse image gives the equality of global sections. -/
theorem scalar_constants (T : Scheme.{u}) (a : integers l E) :
    Γ.map (coefficientMap (scalarMap (l := l) (E := E)) T)
      (constants (B := integers l E) T a) = constants (B := E) T (a : E) := by
  have h : Γ.map (scalarMap (l := l) (E := E))
      (pointConstants (integers l E) a) = pointConstants E (a : E) :=
    Sheaf.Γ_map_ringHomΓSheafCompose (coherentTopology Profinite.{u})
      (scalarRingMap (l := l) (E := E))
      (constantSections (integers l E)) (fun _ _ ↦ rfl)
      (constantSections E) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  apply Γ.ext
  simp only [constants, RingHom.comp_apply, Γ.mapFunctor_hom, Γ.map_hom,
    coefficientMap, Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun b : Γ (Profinite.continuousCoefficientRingObj E) ↦
    CategoryTheory.Functor.LaxMonoidal.ε (upperStarFromPoint T) ≫
    (upperStarFromPoint T).map b.hom) h

/-- Integral scalar restriction is linear for the constant-section actions.
Source: tensor balancing and naturality of constant sections.
(blueprint: lem-weil-pbc-normalized-scalar-actions).
Proof: the scalar compatibility just proved is exactly the hypothesis of
linearity of restriction along a morphism of internal rings. -/
theorem comap_linear (T : Scheme.{u}) :
    letI := modulesLinear (B := integers l E) T
    letI := Mod.linearOfRingHom ((constants (B := E) T).comp (integers l E).subtype)
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (coefficientMap (scalarMap (l := l) (E := E)) T)).Linear (integers l E) :=
  Mod.linear_comap _ _ _ (scalar_constants T)

end WeilConjectures.NormalizedScalar
