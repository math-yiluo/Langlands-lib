/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!

# Open–closed detection and vanishing for module objects over `Λ`

Let `Λ` be a commutative condensed ring, `j : U ⟶ X` an open immersion and `i : Z ⟶ X` a
closed immersion onto the complement of the range of `j`. This file proves, for the module
objects `Mod_{Λ_X}` over `Λ_X = p_X^* Λ`:

* the restrictions `j^*` and `i^*` jointly detect zero objects and isomorphisms
  (`ProEtale.CondensedRing.isZero_of_isZero_upperStar_of_isCompl`,
  `ProEtale.CondensedRing.jointlyReflectIsomorphisms_upperStar_of_isCompl`), from the same
  statement for abelian sheaves
  (`ProEtale.isZero_of_isZero_upperStar_of_isCompl_addCommGrp`, blueprint
  `proposition-extension-zero-restriction-closed-subscheme`);
* the pullback of an extension by zero `j_! M` along a morphism `g` whose range misses the
  range of `j` vanishes
  (`ProEtale.CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint`).

Both reduce to abelian sheaves: the underlying sheaf of `g^* M` is `g^* M` up to isomorphism,
the coefficient comparison `α_g` being an isomorphism, and a module object is zero as soon as
its underlying sheaf is.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [QuasiCompact j]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, for abelian sheaves: let
`i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. A pro-étale
abelian sheaf `F` on `X` with `i^* F = 0` and `j^* F = 0` is zero. -/
theorem isZero_of_isZero_upperStar_of_isCompl_addCommGrp
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Sheaf (ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((i)^*[Ab.{u + 1}].obj F)) (hj : IsZero ((j)^*[Ab.{u + 1}].obj F)) :
    IsZero F := by
  let Y : Bool → Scheme.{u} := fun b ↦ bif b then Z else U
  let g : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => i | false => j
  have : ∀ b, QuasiCompact (g b) := by rintro (_ | _) <;> dsimp [g] <;> infer_instance
  refine (IsZero.iff_id_eq_zero F).2 (eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp g
    (fun x ↦ ?_) (𝟙 F) ?_)
  · by_cases hx : x ∈ Set.range i.base
    · exact ⟨true, hx⟩
    · exact ⟨false, hij.compl_eq ▸ hx⟩
  · rintro (_ | _)
    · exact hj.eq_of_src _ _
    · exact hi.eq_of_src _ _

end ProEtale

namespace ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- A module object over `Λ_X` whose underlying abelian sheaf is zero is zero. -/
lemma isZero_of_isZero_X {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsZero M.X) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact (Mod.forget _).map_injective (hM.eq_of_src _ _)

/-- The underlying abelian sheaf of the pullback `g^* M` of a module object is the pullback
`g^* M` of its underlying sheaf: the extension of scalars along the isomorphism `α_g` is the
restriction of scalars along its inverse. -/
noncomputable def upperStarObjXIso {W X : Scheme.{u}} (g : W ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((g)^*⟦Λ⟧.obj M).X ≅ (g)^*[Ab.{u + 1}].obj M.X :=
  (Mod.forget _).mapIso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).app
      (((g)^*[Ab.{u + 1}].mapMod _).obj M))

/-- **The pullback of an extension by zero along a morphism missing the open vanishes**: for an
open immersion `j : U ⟶ X` and a morphism `g : W ⟶ X` whose ranges are disjoint,
`g^* (j_! M) = 0` for every module object `M` over `Λ_U`. -/
lemma isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint {U W X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hjg : Disjoint (Set.range j.base) (Set.range g.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsZero ((g)^*⟦Λ⟧.obj ((j)_!open⟦Λ⟧.obj M)) :=
  isZero_of_isZero_X Λ ((ProEtale.isZero_upperStar_openImmersionLowerShriek Ab.{u + 1} j g
    (Set.disjoint_iff_inter_eq_empty.1 hjg) M.X).of_iso (upperStarObjXIso Λ g _))

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [QuasiCompact j]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, for module objects over
`Λ`: let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. A module
object `M` over `Λ_X` with `i^* M = 0` and `j^* M = 0` is zero. -/
theorem isZero_of_isZero_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hi : IsZero ((i)^*⟦Λ⟧.obj M)) (hj : IsZero ((j)^*⟦Λ⟧.obj M)) : IsZero M :=
  isZero_of_isZero_X Λ (ProEtale.isZero_of_isZero_upperStar_of_isCompl_addCommGrp i j hij M.X
    (((Mod.forget _).map_isZero hi).of_iso (upperStarObjXIso Λ i M).symm)
    (((Mod.forget _).map_isZero hj).of_iso (upperStarObjXIso Λ j M).symm))

/-- The restrictions to a closed immersion and to its quasi-compact open complement jointly
detect isomorphisms of module objects over `Λ`: both restrictions are exact, so they detect the
vanishing of the kernel and the cokernel
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_of_isCompl`). -/
theorem jointlyReflectIsomorphisms_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    JointlyReflectIsomorphisms (pairFunctor (j)^*⟦Λ⟧ (i)^*⟦Λ⟧) := by
  refine jointlyReflectIsomorphisms_pairFunctor _ _ fun M N φ hj hi ↦ ?_
  have hker {Y : Scheme.{u}} (g : Y ⟶ X) (_ : IsIso ((g)^*⟦Λ⟧.map φ)) :
      IsZero ((g)^*⟦Λ⟧.obj (kernel φ)) :=
    (isZero_kernel_of_mono ((g)^*⟦Λ⟧.map φ)).of_iso (PreservesKernel.iso _ φ)
  have hcoker {Y : Scheme.{u}} (g : Y ⟶ X) (_ : IsIso ((g)^*⟦Λ⟧.map φ)) :
      IsZero ((g)^*⟦Λ⟧.obj (cokernel φ)) :=
    (isZero_cokernel_of_epi ((g)^*⟦Λ⟧.map φ)).of_iso (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (isZero_of_isZero_upperStar_of_isCompl Λ i j hij _ (hker i hi) (hker j hj))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar_of_isCompl Λ i j hij _ (hcoker i hi) (hcoker j hj))
  exact isIso_of_mono_of_epi φ

end ProEtale.CondensedRing

end AlgebraicGeometry
