/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

/-!
# Derived pushforward commutes with `ℚ̄_ℓ ⊗_E -` on bounded below objects

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `f : X ⟶ Y` a morphism of
schemes. The derived comparison **(Push)** `ℚ̄_ℓ,Y ⊗ᴸ Rf_* K ⟶ Rf_*(ℚ̄_ℓ,X ⊗ᴸ K)` for the inclusion
`E̲ ⟶ ℚ̲̄_ℓ` is an isomorphism for every bounded below `K ∈ D(E_X)`, as soon as the underived
(Push) is an isomorphism at injective `E_X`-modules `I` and the underlying abelian sheaves of the
`ℚ̄_ℓ,X ⊗_{E_X} I` are `f_*`-acyclic
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicAlgCl_of_isGE_of_injective`).

The proof is the one of `ProEtale.CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE`:
represent `K` by a bounded below complex `I` of injectives, and use the factorization
`ProEtale.CondensedRing.derivedPushHom_app_Qh_fac` of the derived (Push) at `I` through the
underived one, `ℚ̄_ℓ,X` being flat over `ℤ`
(`ProEtale.preservesFiniteLimits_tensorLeft_padicAlgClRingObj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme DerivedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
  (f : X ⟶ Y)

-- Producing the bounded below injective resolution of `K` is slow to elaborate.
/-- **(Push) for `E ⟶ ℚ̄_ℓ` on bounded below objects**, assuming the underived (Push) is an
isomorphism at injective `E_X`-modules `I` and the `ℚ̄_ℓ,X ⊗_{E_X} I` are `f_*`-acyclic: the
comparison `ℚ̄_ℓ,Y ⊗ᴸ Rf_* K ⟶ Rf_*(ℚ̄_ℓ,X ⊗ᴸ K)` is an isomorphism for bounded below `K`. -/
theorem isIso_derivedPushHom_app_padicAlgCl_of_isGE_of_injective
    (hpush : ∀ (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      Injective I → IsIso ((pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app I))
    (hacyc : ∀ (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      Injective I → ((f)_*[Ab.{u + 1}]).rightAcyclic
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj I).X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K) := by
  -- `have` first: `obtain` on the term itself would abstract it over the large goal.
  have hK := K.exists_iso_Q_obj_of_isGE n
  obtain ⟨T, _, ⟨e⟩⟩ := hK
  have hT := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective T n
  obtain ⟨I, i, _, hI, _⟩ := hT
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I n
  rw [NatTrans.isIso_app_iff_of_iso _
    (e ≪≫ asIso (Q.map i) ≪≫ ((quotientCompQhIso _).app I).symm)]
  dsimp only [Functor.comp_obj]
  have h := derivedPushHom_app_Qh_fac (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f I
  have : ∀ k, IsIso (((NatTrans.mapHomologicalComplex
      (pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) (ComplexShape.up ℤ)).app I).f
        k) := fun k ↦ hpush (I.X k) (hI k)
  have : IsIso ((NatTrans.mapHomologicalComplex
      (pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) (ComplexShape.up ℤ)).app I) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((NatTrans.mapHomotopyCategory
      (pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient _ _).obj I)) :=
    Functor.map_isIso (HomotopyCategory.quotient _ _) ((NatTrans.mapHomologicalComplex
      (pushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) (ComplexShape.up ℤ)).app I)
  have : CochainComplex.IsStrictlyGE ((Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I) n :=
    (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi ↦
      show IsZero ((Mod.extendScalars _).obj (I.X i)) from
        Functor.map_isZero _ (I.isZero_of_isStrictlyGE n i hi)
  have : IsIso (((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).rightDerivedFunctorUnit.app
      (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ _).obj I))) :=
    Functor.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE _ ((Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I) n fun k ↦
      rightAcyclic_lowerStar_of_rightAcyclic_forget _ f (hacyc (I.X k) (hI k))
  have := IsIso.of_isIso_fac_left h
  have := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this
  -- The goal and `this` differ only in proofs inside instance arguments; at default
  -- transparency the unifier unfolds those instances (about 40 s), at reducible transparency it
  -- compares their arguments.
  with_reducible exact this

variable [QuasiCompact f] [QuasiSeparated f]

/-- **(Push) for `E ⟶ ℚ̄_ℓ` on bounded below objects, given the finite stages**: for a
quasi-compact quasi-separated `f`, the comparison `ℚ̄_ℓ,Y ⊗ᴸ Rf_* K ⟶ Rf_*(ℚ̄_ℓ,X ⊗ᴸ K)` is an
isomorphism for bounded below `K`, as soon as, for every finite subextension `F ⊇ E` and every
injective `E_X`-module `I`, the underived (Push) `F_Y ⊗ f_* I ⟶ f_*(F_X ⊗ I)` is an isomorphism
and the underlying abelian sheaf of `F_X ⊗_{E_X} I` is `f_*`-acyclic. -/
theorem isIso_derivedPushHom_app_padicAlgCl_of_isGE
    (hpush : ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (hF : E ≤ F)
      (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      Injective I → IsIso ((pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f).app I))
    (hacyc : ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (hF : E ≤ F)
      (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)),
      Injective I → ((f)_*[Ab.{u + 1}]).rightAcyclic
        ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).obj I).X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K) :=
  isIso_derivedPushHom_app_padicAlgCl_of_isGE_of_injective ℓ E f
    (fun I hI ↦ isIso_pushHom_padicSubfieldRingObjToPadicAlgCl_app ℓ E f I
      fun F hF ↦ hpush F hF I hI)
    (fun I hI ↦ rightAcyclic_lowerStar_extendScalars_padicAlgCl ℓ E f I
      fun F hF ↦ hacyc F hF I hI) K n

end AlgebraicGeometry.ProEtale.CondensedRing
