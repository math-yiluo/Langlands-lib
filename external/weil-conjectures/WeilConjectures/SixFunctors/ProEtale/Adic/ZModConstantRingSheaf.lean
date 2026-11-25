/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit

/-!
# The constant pro-étale ring sheaf `ℤ/N` is the sheaf of locally constant functions

Let `X` be a scheme and `N` a natural number. On the small pro-étale site of `X`, the
sheafification of the constant presheaf of rings with value `ℤ/N` is, as a ring object of the
category of abelian sheaves, the sheaf `(ℤ/N)_X = C(-, ℤ/N)` of locally constant functions
(`AlgebraicGeometry.ProEtale.zmodConstSheafRingIso`). Indeed the constant functions
`ℤ/N ⟶ C(U, ℤ/N)` form a locally bijective morphism of presheaves: a continuous map to the
discrete ring `ℤ/N` is constant on the members of the Zariski cover by its fibres, and two
distinct constants only agree on the empty scheme, which is covered by the empty family.

## Main definitions

- `AlgebraicGeometry.ProEtale.zmodConstPresheaf`: the constant presheaf of rings `ℤ/N`.
- `AlgebraicGeometry.ProEtale.zmodConstToContinuousMap`: the constant functions
  `ℤ/N ⟶ C(-, ℤ/N)`.
- `AlgebraicGeometry.ProEtale.zmodConstSheafRingIso`: the isomorphism of ring objects between
  the sheafification of `ℤ/N` and `(ℤ/N)_X`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (X : Scheme.{u}) (N : ℕ)

/-- The constant presheaf of rings with value `ℤ/N` on the small pro-étale site of `X`. -/
noncomputable abbrev zmodConstPresheaf : X.ProEtᵒᵖ ⥤ RingCat.{u + 1} :=
  (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N)))

/-- The constant functions, as a morphism of presheaves of rings from the constant presheaf
`ℤ/N` to the sheaf of locally constant functions `U ↦ C(U, ℤ/N)`. -/
noncomputable def zmodConstToContinuousMap :
    zmodConstPresheaf X N ⟶ (continuousMapRingSheaf X (ZMod N)).obj where
  app U := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((ContinuousMap.C (α := U.unop.left)).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- The constant functions send `a` to the constant function `a`. -/
lemma zmodConstToContinuousMap_app_apply (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} (ZMod N)) :
    (zmodConstToContinuousMap X N).app U a = ULift.up (ContinuousMap.const _ a.down) :=
  rfl

/-- A continuous function to the discrete ring `ℤ/N` is locally constant: it is constant on its
open fibres, which form a Zariski cover. -/
instance : Presheaf.IsLocallySurjective (ProEt.topology X)
    (Functor.whiskerRight (zmodConstToContinuousMap X N) (forget₂ RingCat.{u + 1} Ab.{u + 1})) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, ZMod N) := (s₀ : ULift.{u + 1} C(U.left, ZMod N)).down
    let j (m : ULift.{u} (ZMod N)) := (U.left.fiberOpens s m.down).ι
    refine ProEt.mem_topology_of_openImmersion _ j (fun x ↦ ⟨⟨s x⟩, ⟨x, rfl⟩, ?_⟩) fun m ↦ ?_
    · exact Scheme.Opens.ι_apply _ _
    · refine ⟨ULift.up m.down, ULift.ext (ContinuousMap.ext fun x ↦ ?_)⟩
      exact x.2.symm

/-- Two constant sections agreeing on `U` agree locally: either they are equal, or `U` is empty
and is covered by the empty family. -/
instance : Presheaf.IsLocallyInjective (ProEt.topology X)
    (Functor.whiskerRight (zmodConstToContinuousMap X N) (forget₂ RingCat.{u + 1} Ab.{u + 1})) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact (ProEt.topology X).superset_covering (fun _ _ _ ↦ rfl)
        ((ProEt.topology X).top_mem _)
    · have : IsEmpty U.unop.left := ⟨fun x ↦ hab (by
        have := congr_arg (fun f : ULift.{u + 1} C(U.unop.left, ZMod N) ↦ f.down x) h
        exact ULift.ext this)⟩
      exact ProEt.mem_topology_of_openImmersion _ (fun _ : PEmpty.{u + 1} ↦ 𝟙 U.unop.left)
        (fun x ↦ isEmptyElim x) fun i ↦ i.elim

/-- The morphism of abelian sheaves from the sheafification of the constant presheaf `ℤ/N` to
`(ℤ/N)_X = C(-, ℤ/N)` induced by the constant functions. -/
noncomputable def zmodConstSheafToContinuousMap :
    Sheaf.sheafifyRingPresheaf (ProEt.topology X) (zmodConstPresheaf X N) ⟶
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (ZMod N)) :=
  ((sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerRight (zmodConstToContinuousMap X N) (forget₂ RingCat.{u + 1} Ab.{u + 1}))

/-- `ProEtale.zmodConstSheafToContinuousMap` is the sheafification of the constant functions
followed by the counit of the sheafification adjunction. -/
lemma zmodConstSheafToContinuousMap_eq :
    zmodConstSheafToContinuousMap X N =
      (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
        (Functor.whiskerRight (zmodConstToContinuousMap X N)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
        (Sheaf.sheafifyRingPresheafIso (ProEt.topology X)
          (continuousMapRingSheaf X (ZMod N))).hom :=
  Adjunction.homEquiv_counit _ _ _ _

/-- The comparison from the sheafified constant ring `ℤ/N` is a morphism of ring objects. -/
instance : IsMonHom (zmodConstSheafToContinuousMap X N) := by
  rw [zmodConstSheafToContinuousMap_eq]
  infer_instance

/-- The comparison restricted along the unit of sheafification is the constant functions map. -/
lemma toSheafify_zmodConstSheafToContinuousMap :
    toSheafify (ProEt.topology X) _ ≫ (zmodConstSheafToContinuousMap X N).hom =
      Functor.whiskerRight (zmodConstToContinuousMap X N) (forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
  have h := ((sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).homEquiv _
    ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X (ZMod N)))).apply_symm_apply
    (Functor.whiskerRight (zmodConstToContinuousMap X N) (forget₂ RingCat.{u + 1} Ab.{u + 1}))
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

/-- The comparison is an isomorphism, the constant functions being locally bijective. -/
instance : IsIso (zmodConstSheafToContinuousMap X N) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have h := toSheafify_zmodConstSheafToContinuousMap X N
  refine (Sheaf.isLocallyBijective_iff_isIso (zmodConstSheafToContinuousMap X N)).1 ⟨?_, ?_⟩
  · refine (Presheaf.comp_isLocallyInjective_iff _ (toSheafify (ProEt.topology X) _) _).1 ?_
    rw [h]
    infer_instance
  · refine (Presheaf.comp_isLocallySurjective_iff _ (toSheafify (ProEt.topology X) _) _).1 ?_
    rw [h]
    infer_instance

/-- **The constant ring sheaf `ℤ/N` is the sheaf of locally constant functions**: the
sheafification of the constant presheaf of rings `ℤ/N` is isomorphic, as a ring object, to
`(ℤ/N)_X = C(-, ℤ/N)`. -/
noncomputable def zmodConstSheafRingIso :
    Sheaf.sheafifyRingPresheaf (ProEt.topology X) (zmodConstPresheaf X N) ≅
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (ZMod N)) :=
  asIso (zmodConstSheafToContinuousMap X N)

/-- The isomorphism `ProEtale.zmodConstSheafRingIso` is an isomorphism of ring objects. -/
instance : IsMonHom (zmodConstSheafRingIso X N).hom :=
  inferInstanceAs (IsMonHom (zmodConstSheafToContinuousMap X N))

/-- The inverse of `ProEtale.zmodConstSheafRingIso` is a morphism of ring objects. -/
instance : IsMonHom (zmodConstSheafRingIso X N).inv :=
  inferInstance

end AlgebraicGeometry.ProEtale
