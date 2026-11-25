/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Blowup.Complement
public import WeilConjectures.Blowup.Principalization
public import WeilConjectures.Blowup.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.TraceFormula.OpenClosedTriangle
public import WeilConjectures.TraceFormula.Specialization.DefectLocal

/-!

# Reduction of the defect to a Cartier divisor

Let `X` be a separated `k`-scheme of finite type, `I` an ideal sheaf on `X` with centre
`i : Z = V(I) ⟶ X`, and `b : X' = Bl_Z X ⟶ X` the blow-up of `X` along `I`
(`ProEtale.CondensedRing.blowupOverHom`). The pullback `b^* I` is invertible
(`ProEtale.CondensedRing.isInvertible_comap_blowupOverHom`), so `Z' = b⁻¹ Z` is an effective
Cartier divisor of `X'`.

This file proves (blueprint `theorem-verdier-s-theorem-specialization-zero`) that the defect
`C_{X,Z}(L)` of a bounded constructible complex `L` with `Li^* L = 0` is computed on the blow-up:
`C_{X,Z}(L) ≅ Rb_{Z*} C_{X',Z'}(Lb^* L)`
(`ProEtale.CondensedRing.nonempty_specializationDefect_iso_blowup`).

The proof constructs some isomorphism `L ≅ Rb_* Lb^* L`: both sides vanish after `Li^*` (for the
right-hand side by proper base change), so both are the extension by zero of their restriction to
the complement `U = X ∖ Z` (the open–closed triangle), and these restrictions agree by proper base
change, `b` being an isomorphism over `U`. The proper exchange for the defect
(`ProEtale.CondensedRing.nonempty_specializationDefect_lowerStar_iso`) then concludes.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Pullback and pushforward along an isomorphism -/

section Iso

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {A B : Over (Spec (.of k))}
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]

/-- Along an isomorphism `e`, `Re_* ∘ Le^*` is isomorphic to the identity: `Re_*` is the right
adjoint of the equivalence `Le^*`, hence isomorphic to its inverse. -/
noncomputable def boundedConstructibleUpperStarLowerStarIsoOfIsIso (e : A ⟶ B) [IsIso e] :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e ⋙
        boundedConstructibleLowerStar ℓ e ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft _
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ e).rightAdjointUniq
      (boundedConstructibleUpperStarEquivalenceOfIsIso ℓ e).toAdjunction) ≪≫
    (boundedConstructibleUpperStarEquivalenceOfIsIso ℓ e).unitIso.symm

end Iso

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-! ### The blow-up as a `k`-scheme -/

/-- The blow-up `X' = Bl_Z X` of `X` along `I`, as a `k`-scheme. -/
noncomputable def blowupOver : Over (Spec (.of k)) :=
  Over.mk (I.blowupMap ≫ X.hom)

/-- The blow-up morphism `b : X' = Bl_Z X ⟶ X`. -/
noncomputable def blowupOverHom : blowupOver X I ⟶ X :=
  Over.homMk I.blowupMap rfl

@[simp]
lemma blowupOverHom_left : (blowupOverHom X I).left = I.blowupMap :=
  rfl

instance [LocallyOfFiniteType X.hom] : IsProper (blowupOverHom X I).left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact inferInstanceAs (IsProper I.blowupMap)

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (blowupOver X I).hom :=
  inferInstanceAs (LocallyOfFiniteType ((blowupOverHom X I).left ≫ X.hom))

instance [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : QuasiCompact (blowupOver X I).hom :=
  inferInstanceAs (QuasiCompact ((blowupOverHom X I).left ≫ X.hom))

instance [LocallyOfFiniteType X.hom] [IsSeparated X.hom] : IsSeparated (blowupOver X I).hom :=
  inferInstanceAs (IsSeparated ((blowupOverHom X I).left ≫ X.hom))

/-- The pullback of `I` to the blow-up is invertible: `Z' = b⁻¹ Z` is an effective Cartier
divisor. -/
theorem isInvertible_comap_blowupOverHom : (I.comap (blowupOverHom X I).left).IsInvertible :=
  I.isInvertible_comap_blowupMap

/-- The centre of `X'` is the inverse image of the centre of `X`. -/
lemma isPullback_centreι_blowupOverHom :
    IsPullback (centreι (blowupOver X I) (I.comap (blowupOverHom X I).left))
      (centreMap (blowupOverHom X I) I) (blowupOverHom X I) (centreι X I) := by
  have h : IsPullback (I.comap (blowupOverHom X I).left).subschemeι
      (IdealSheafData.subschemeMap _ _ (blowupOverHom X I).left
        (I.le_map_comap (blowupOverHom X I).left))
      (blowupOverHom X I).left I.subschemeι :=
    IsPullback.of_iso_pullback
      ⟨(IdealSheafData.subschemeMap_subschemeι _ _ _ (I.le_map_comap _)).symm⟩
      (I.comapIso _) (I.comapIso_hom_fst _) (I.comapIso_hom_snd _)
  exact IsPullback.of_map (Over.forget _) (centreMap_centreι _ _).symm h.flip.flip

/-! ### The complement of the centre -/

/-- The inverse image `b⁻¹ U` of the complement `U = X ∖ Z` of the centre in the blow-up. -/
noncomputable abbrev blowupCentreComplOpens : (blowupOver X I).left.Opens :=
  (blowupOverHom X I).left ⁻¹ᵁ I.support.compl

/-- The restriction `b_U : b⁻¹ U ⟶ U` of the blow-up morphism, an isomorphism. -/
noncomputable def blowupCentreComplRestrict :
    overRestrict (blowupOver X I) (blowupCentreComplOpens X I) ⟶ overRestrict X I.support.compl :=
  Over.homMk ((blowupOverHom X I).left ∣_ I.support.compl) (by
    change _ ≫ Scheme.Opens.ι I.support.compl ≫ X.hom = _
    rw [morphismRestrict_ι_assoc]
    rfl)

instance : IsIso (blowupCentreComplRestrict X I) := by
  have : IsIso ((Over.forget _).map (blowupCentreComplRestrict X I)) :=
    I.isIso_blowupMap_restrict_support_compl
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The blow-up restricted over the complement of the centre is a base change of the blow-up:
```
b⁻¹ U ⟶ X'
  │      │
  U  ⟶   X
```
-/
lemma isPullback_blowupCentreComplRestrict :
    IsPullback (overRestrictι (blowupOver X I) (blowupCentreComplOpens X I))
      (blowupCentreComplRestrict X I) (blowupOverHom X I) (overRestrictι X I.support.compl) := by
  have w : blowupCentreComplRestrict X I ≫ overRestrictι X I.support.compl =
      overRestrictι (blowupOver X I) (blowupCentreComplOpens X I) ≫ blowupOverHom X I := by
    ext1
    exact morphismRestrict_ι _ _
  exact (IsPullback.of_map (Over.forget _) w
    (isPullback_morphismRestrict (blowupOverHom X I).left I.support.compl)).flip

/-! ### The reduction -/

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- A bounded constructible complex with `Li^* K = 0` is the extension by zero of its restriction
to the complement of the centre: the counit `j_! j^* K ⟶ K` is an isomorphism. -/
lemma isIso_counit_overRestrictι_of_isZero (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj K)) :
    IsIso ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ
      (overRestrictι X I.support.compl)).counit.app K) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openClosed_boundedConstructible ℓ
    (isCompl_range_overRestrictι_centreι I) K
  have h : IsZero ((boundedConstructibleLowerStar ℓ (centreι X I)).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (centreι X I)).obj K)) :=
    Functor.map_isZero _ hK
  exact (Triangle.isZero₃_iff_isIso₁ _ hδ).1 h

/-- If `Li^* L = 0`, then `Li^* Rb_* Lb^* L = 0`, by proper base change along the inverse image
`Z' ⟶ Z` of the centre. -/
lemma isZero_upperStar_centreι_lowerStar_blowupOverHom
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (centreι X I)).obj
      ((boundedConstructibleLowerStar ℓ (blowupOverHom X I)).obj
        ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L))) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
    (isPullback_centreι_blowupOverHom X I)
  refine IsZero.of_iso ?_ ((asIso (boundedConstructibleBaseChange ℓ
    (isPullback_centreι_blowupOverHom X I).toCommSq)).app
      ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L))
  refine Functor.map_isZero (boundedConstructibleLowerStar ℓ (centreMap (blowupOverHom X I) I)) ?_
  refine IsZero.of_iso ?_ ((boundedConstructibleUpperStarComp _ ℓ
    (centreι (blowupOver X I) (I.comap (blowupOverHom X I).left)) (blowupOverHom X I)).app L).symm
  rw [← centreMap_centreι]
  exact IsZero.of_iso
    (Functor.map_isZero (boundedConstructibleUpperStar _ ℓ (centreMap (blowupOverHom X I) I)) hL)
    ((boundedConstructibleUpperStarComp _ ℓ (centreMap (blowupOverHom X I) I) (centreι X I)).app L)

/-- The restrictions of `L` and `Rb_* Lb^* L` to the complement `U` of the centre agree, by proper
base change, `b` being an isomorphism over `U`. -/
noncomputable def upperStarOverRestrictιLowerStarBlowupOverHomIso
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X I.support.compl)).obj
        ((boundedConstructibleLowerStar ℓ (blowupOverHom X I)).obj
          ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L)) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X I.support.compl)).obj L :=
  haveI := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
    (isPullback_blowupCentreComplRestrict X I)
  (asIso (boundedConstructibleBaseChange ℓ
      (isPullback_blowupCentreComplRestrict X I).toCommSq)).app
      ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L) ≪≫
    (boundedConstructibleLowerStar ℓ (blowupCentreComplRestrict X I)).mapIso
      (((boundedConstructibleUpperStarComp _ ℓ
          (overRestrictι (blowupOver X I) (blowupCentreComplOpens X I))
          (blowupOverHom X I)).app L).symm ≪≫
        eqToIso (by rw [(isPullback_blowupCentreComplRestrict X I).w]) ≪≫
        (boundedConstructibleUpperStarComp _ ℓ (blowupCentreComplRestrict X I)
          (overRestrictι X I.support.compl)).app L) ≪≫
    (boundedConstructibleUpperStarLowerStarIsoOfIsIso ℓ (blowupCentreComplRestrict X I)).app
      ((boundedConstructibleUpperStar _ ℓ (overRestrictι X I.support.compl)).obj L)

/-- If `Li^* L = 0`, then `L ≅ Rb_* Lb^* L`: both are the extension by zero of their (isomorphic)
restrictions to the complement of the centre. -/
noncomputable def lowerStarUpperStarBlowupOverHomIso
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    L ≅ (boundedConstructibleLowerStar ℓ (blowupOverHom X I)).obj
      ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L) :=
  haveI := isIso_counit_overRestrictι_of_isZero X I L hL
  haveI := isIso_counit_overRestrictι_of_isZero X I _
    (isZero_upperStar_centreι_lowerStar_blowupOverHom X I L hL)
  (asIso ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ
      (overRestrictι X I.support.compl)).counit.app L)).symm ≪≫
    (boundedConstructibleLowerShriek ℓ (overRestrictι X I.support.compl)).mapIso
      (upperStarOverRestrictιLowerStarBlowupOverHomIso X I L).symm ≪≫
    asIso ((boundedConstructibleLowerShriekUpperStarAdjunction_padicAlgCl ℓ
      (overRestrictι X I.support.compl)).counit.app _)

/-- **Reduction of the defect to a Cartier divisor** (blueprint
`theorem-verdier-s-theorem-specialization-zero`): for `L` bounded constructible on `X` with
`Li^* L = 0` and `b : X' ⟶ X` the blow-up along `I`, `C_{X,Z}(L) ≅ Rb_{Z*} C_{X',Z'}(Lb^* L)`, where
`Z' = V(b^* I)` is an effective Cartier divisor
(`ProEtale.CondensedRing.isInvertible_comap_blowupOverHom`). Here the isomorphism is only asserted
to exist. -/
theorem nonempty_specializationDefect_iso_blowup
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    Nonempty (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj ≅
      R(((centreSpecialFibreMap (blowupOverHom X I) I k').left)_*⟦
        Profinite.padicAlgClRingObj ℓ⟧).obj
        (specializationDefect (blowupOver X I) (I.comap (blowupOverHom X I).left) k'
          (Profinite.padicAlgClRingObj ℓ)
          ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L).obj)) := by
  obtain ⟨e⟩ := nonempty_specializationDefect_iso X I k' (Profinite.padicAlgClRingObj ℓ)
    ((boundedConstructible _).ι.mapIso (lowerStarUpperStarBlowupOverHomIso X I L hL) ≪≫
      (boundedConstructibleLowerStarCompatibility ℓ (blowupOverHom X I)).app
        ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L))
  obtain ⟨e'⟩ := nonempty_specializationDefect_lowerStar_iso (blowupOverHom X I) I k'
    ((boundedConstructibleUpperStar _ ℓ (blowupOverHom X I)).obj L)
  exact ⟨e ≪≫ e'⟩

end AlgebraicGeometry.ProEtale.CondensedRing
