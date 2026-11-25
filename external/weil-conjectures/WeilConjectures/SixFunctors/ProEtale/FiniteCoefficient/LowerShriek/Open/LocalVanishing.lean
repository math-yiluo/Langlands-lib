/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection

/-!
# Sections of an extension by zero vanish near the complement

Let `j : U ⟶ X` be an open immersion and `F` a pro-étale sheaf of modules on `U`. A section of
the extension by zero `j_! F` over `V` vanishes on a weakly étale neighbourhood of every point of
`V` lying over the complement of `U`
(`AlgebraicGeometry.ProEtale.exists_map_eq_zero_openImmersionLowerShriek`). Indeed `j_! F` is the
sheafification of the presheaf extension by zero, so the section locally comes from the presheaf
extension by zero, whose sections over a `V'` not factoring through `U` vanish.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R : Type (u + 1)} [Ring R] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Sections of `j_! F` vanish near the complement of `U`.** A section `s` of the extension
by zero `j_! F` over `V` vanishes on a weakly étale neighbourhood `V' ⟶ V` of each point `x` of
`V` lying over the complement of `U`. -/
lemma exists_map_eq_zero_openImmersionLowerShriek
    (F : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) {V : X.ProEt}
    (s : ToType (((j)_!open[ModuleCat.{u + 1} R].obj F).obj.obj (op V))) (x : V.left)
    (hx : V.hom.base x ∉ Set.range j.base) :
    ∃ (V' : X.ProEt) (f : V' ⟶ V), x ∈ Set.range f.left.base ∧
      ((j)_!open[ModuleCat.{u + 1} R].obj F).obj.map f.op s = 0 := by
  set L := openImmersionLocalization j
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) (L.op.leftKanExtension F.obj)) :=
    Presheaf.isLocallySurjective_toSheafify' (J := ProEt.topology X) _
  have hS := Presheaf.imageSieve_mem (ProEt.topology X)
    (toSheafify (ProEt.topology X) (L.op.leftKanExtension F.obj)) s
  obtain ⟨P, hP, hle⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨ι, T, φ, rfl⟩ := P.exists_eq_ofArrows
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
  obtain ⟨i, y, hy⟩ := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 hP.2).1 x
  refine ⟨T i, φ i, ⟨y, hy⟩, ?_⟩
  obtain ⟨t, ht⟩ := hle _ _ (Presieve.ofArrows.mk i)
  have : IsEmpty (CostructuredArrow L.op (op (T i))) := by
    refine ⟨fun c ↦ hx ⟨(c.left.unop.hom).base ((c.hom.unop.left).base y), ?_⟩⟩
    have h₁ := MorphismProperty.Over.w c.hom.unop
    have h₂ := MorphismProperty.Over.w (φ i)
    change (c.hom.unop.left ≫ c.left.unop.hom ≫ j) = (T i).hom at h₁
    rw [← hy]
    exact (congrArg (fun f ↦ f.base y) h₁).trans (congrArg (fun f ↦ f.base y) h₂).symm
  have hI := (isColimitEquivIsInitialOfIsEmpty _ _).1
    (L.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (op (T i)))
  have : Subsingleton (ToType ((L.op.leftKanExtension F.obj).obj (op (T i)))) :=
    ModuleCat.subsingleton_of_isZero hI.isZero
  change ConcreteCategory.hom ((sheafify (ProEt.topology X) (L.op.leftKanExtension F.obj)).map
    (φ i).op) s = 0
  rw [← ht, Subsingleton.elim t 0, map_zero]

section Mono

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The unit `j_! F ⟶ j_* j^* j_! F` of the pullback along an open immersion is a monomorphism:
the comparison `j_! F ⟶ j_* F` factors through it. -/
instance mono_upperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
    (F : Sheaf (ProEt.topology U) A) :
    Mono ((upperStarLowerStarAdjunction A j).unit.app ((j)_!open[A].obj F)) := by
  let adj := openImmersionRestrictionLowerStarAdjunction A j
  have h₂ : Mono (adj.unit.app ((j)_!open[A].obj F)) := by
    have h := adj.homEquiv_unit (X := (j)_!open[A].obj F) (Y := F)
      ((adj.homEquiv _ _).symm ((openImmersionLowerShriekToLowerStar A j).app F))
    rw [Equiv.apply_symm_apply] at h
    exact mono_of_mono_fac h.symm
  exact mono_of_mono_fac (Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction A j) adj ((j)_!open[A].obj F))

end Mono

end AlgebraicGeometry.ProEtale
