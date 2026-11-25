/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Associativity

/-!
# The compact support formalism of the bounded below étale derived categories

The bounded below derived categories `D⁺(X_ét, A)` of étale sheaves, with the pullbacks `D⁺(f^*)`,
the derived pushforwards `R⁺f_*` and the extensions by zero `D⁺(j_!)` along open immersions,
form a `AlgebraicGeometry.CompactSupportFormalism`, `Etale.derivedPlusFormalism A`. Its compactly
supported direct image along a compactification `c` is `Rf_!(c)[A]+`, and its compactly supported
direct image along a morphism admitting a compactification is `R(f)_![A]+`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

omit [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] in
lemma upperStarCompDerivedPlus_hom_app_congr {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (d d' : T ⟶ R) (hd : d = h₁ ≫ h₂) (hd' : d' = h₁ ≫ h₂)
    (M : DerivedCategory.Plus (Sheaf R.smallEtaleTopology A)) :
    (upperStarCompDerivedPlus A h₁ h₂ d hd).hom.app M =
      eqToHom (by rw [hd, hd']) ≫ (upperStarCompDerivedPlus A h₁ h₂ d' hd').hom.app M := by
  subst hd hd'
  simp

include A in
/-- **The compact support formalism of the bounded below étale derived categories**: the
categories `D⁺(X_ét, A)`, the pullbacks `D⁺(f^*)` with their composition isomorphisms
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus`, the derived pushforwards `R⁺f_*` and the
extensions by zero `D⁺(j_!)` along open immersions. -/
noncomputable def derivedPlusFormalism : CompactSupportFormalism where
  obj X := DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)
  pb f := D+((f)^*[A])
  pbId X := upperStarIdDerivedPlus A X
  pbComp f g := upperStarCompDerivedPlus A f g
  pbComp_assoc f g h M := by
    have := NatTrans.congr_app (upperStarCompDerivedPlus_assoc A f g h (f ≫ g) (g ≫ h)
      ((f ≫ g) ≫ h) rfl rfl rfl) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at this
    rw [← this, upperStarCompDerivedPlus_hom_app_congr A f (g ≫ h) _ (f ≫ g ≫ h)
      (Category.assoc _ _ _) rfl]
    simp
  pbId_comp f M := by
    have := NatTrans.congr_app (upperStarCompDerivedPlus_id_left A f) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at this
    rw [upperStarCompDerivedPlus_hom_app_congr A (𝟙 _) f _ f (by simp) (by simp), Category.assoc,
      this]
    simp
  pbComp_id f M := by
    have := NatTrans.congr_app (upperStarCompDerivedPlus_id_right A f) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at this
    rw [upperStarCompDerivedPlus_hom_app_congr A f (𝟙 _) _ f (by simp) (by simp), Category.assoc,
      this]
    simp
  pf f := R+((f)_*[A])
  adj f := (upperStarLowerStarAdjunction A f).derivedPlus
  sh j hj := haveI := hj.out; D+((j)_!open[A])
  shAdj j hj := haveI := hj.out
    (openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryPlusAdjunction

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The compactly supported direct image of the formalism `derivedPlusFormalism A` along a
compactification `c` is `Rf_!(c)[A]+`. -/
lemma derivedPlusFormalism_shriek (c : Compactification f) :
    (derivedPlusFormalism A).shriek c = Rf_!(c)[A]+ :=
  rfl

/-- The compactly supported direct image of the formalism `derivedPlusFormalism A` along a
morphism admitting a compactification is `R(f)_![A]+`. -/
lemma derivedPlusFormalism_lowerShriek [HasCompactification f] :
    (derivedPlusFormalism A).lowerShriek f = R(f)_![A]+ :=
  rfl


section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- **Open–closed conservativity on the bounded below derived categories**: a morphism which is
an isomorphism after restriction to an open `j` and whose source and target vanish on the closed
complement of `j` is an isomorphism. -/
lemma isIso_of_isIso_plus_of_isZero {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    {K K' : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') (hj : IsIso (D+((j)^*[ModuleCat.{u + 1} Λ]).map φ))
    (hK : IsZero (D+((j.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj K))
    (hK' : IsZero (D+((j.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj K')) : IsIso φ := by
  suffices IsIso (DerivedCategory.Plus.ι.map φ) from
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  refine isIso_of_isIso_mapDerivedCategoryUpperStar_map _ j j.closedComplement
    j.range_closedComplement _ ?_ ?_
  · exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map
      (D+((j)^*[ModuleCat.{u + 1} Λ]).map φ)))
  · exact isIso_of_source_target_iso_zero _
      (DerivedCategory.Plus.ι.mapIso hK.isoZero ≪≫ DerivedCategory.Plus.ι.mapZeroObject)
      (DerivedCategory.Plus.ι.mapIso hK'.isoZero ≪≫ DerivedCategory.Plus.ι.mapZeroObject)

omit [Finite Λ] in
lemma isZero_plus_upperStar_openImmersionLowerShriek {U W Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (i : W ⟶ Z) (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero (D+((i)^*[ModuleCat.{u + 1} Λ]).obj (D+((j)_!open[ModuleCat.{u + 1} Λ]).obj K)) :=
  IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _
    (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ j i hij
      (DerivedCategory.Plus.ι.obj K))

omit [Finite Λ] in
lemma isZero_plus_upperStar_upperStar_openImmersionLowerShriek {U W Z Z' : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j] (b : Z' ⟶ Z) (i : W ⟶ Z')
    (hij : Disjoint (Set.range (i ≫ b).base) (Set.range j.base))
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero (D+((i)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((b)^*[ModuleCat.{u + 1} Λ]).obj (D+((j)_!open[ModuleCat.{u + 1} Λ]).obj K))) :=
  IsZero.of_iso (isZero_plus_upperStar_openImmersionLowerShriek Λ j (i ≫ b) hij K)
    ((upperStarCompDerivedPlus _ i b).app _).symm

/-- **Base change for the extension by zero** in the bounded below étale derived categories:
the base change map of a cartesian square is an isomorphism. It is checked on the open `l` and on
its closed complement, by open–closed conservativity. -/
instance : (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).HasBaseChange where
  isIso_baseChange {U' U Z' Z t l r b} _ _ h := by
    have hdisj' : Disjoint (Set.range (l.closedComplement ≫ b).base) (Set.range r.base) := by
      rw [Set.disjoint_left]
      rintro _ ⟨w, rfl⟩ hw
      have hl : l.closedComplement w ∈ Set.range l := by
        rw [Scheme.range_snd_of_isPullback h]
        exact hw
      have hw' : l.closedComplement.base w ∈ (Set.range l.base)ᶜ := by
        rw [← l.range_closedComplement]; exact ⟨w, rfl⟩
      exact hw' hl
    have : IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shAdj r).unit :=
      isIso_derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus_unit Λ r
    have : IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shAdj l).unit :=
      isIso_derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus_unit Λ l
    have (M : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
        IsIso (((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).baseChange t l r b h.w).app
          M) :=
      isIso_of_isIso_plus_of_isZero Λ l _
        ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).isIso_map_baseChange_app t l r b h.w M)
        (isZero_plus_upperStar_openImmersionLowerShriek Λ l _
          (by rw [l.range_closedComplement]; exact disjoint_compl_left) _)
        (isZero_plus_upperStar_upperStar_openImmersionLowerShriek Λ r b _ hdisj' M)
    exact NatIso.isIso_of_isIso_app _


omit [Finite Λ] in
/-- In a cartesian square `t ≫ r = l ≫ b` with `b` proper and torsion coefficients, `b_*` of an
extension by zero along `l` vanishes on the closed complement of `r`: by proper base change it is
computed on `b⁻¹` of the closed complement, which does not meet `l`. -/
lemma isZero_plus_upperStar_lowerStar_openImmersionLowerShriek (hΛ : IsAddTorsion Λ)
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z} {b : Z' ⟶ Z}
    [IsOpenImmersion l] [IsOpenImmersion r] [IsProper b] (h : IsPullback t l r b)
    (M : DerivedCategory.Plus (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero (D+((r.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj
      (R+((b)_*[ModuleCat.{u + 1} Λ]).obj (D+((l)_!open[ModuleCat.{u + 1} Λ]).obj M))) := by
  let sq := IsPullback.of_hasPullback b r.closedComplement
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛ sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  have hdisj :
      Disjoint (Set.range (pullback.fst b r.closedComplement).base) (Set.range l.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨u, hu⟩
    have h₁ : b.base ((pullback.fst b r.closedComplement).base p) ∈ Set.range r.base := by
      refine ⟨t.base u, ?_⟩
      rw [← hu, ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    have h₂ : b.base ((pullback.fst b r.closedComplement).base p) ∈ (Set.range r.base)ᶜ := by
      rw [← r.range_closedComplement, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact h₂ h₁
  exact IsZero.of_iso
    (((pullback.snd b r.closedComplement)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus
      |>.map_isZero (isZero_plus_upperStar_openImmersionLowerShriek Λ l _ hdisj M))
    (asIso ((Etale.derivedBaseChangeMapPlus _ sq.toCommSq).app _))

/-- **Proper base change for the compactly supported direct image**: in the bounded below étale
derived categories with finite coefficients, the exchange map `r_! t_* ⟶ b_* l_!` of a cartesian
square with `b` proper is an isomorphism. On the open `r` this is formal; on its closed complement
both sides vanish, by proper base change
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`,
blueprint `theorem-proper-base-change-classical-pro`). -/
instance : (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).HasProperExchange where
  isIso_exchange {U' U Z' Z t l r b} _ _ _ h := by
    have := CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := derivedPlusFormalism (ModuleCat.{u + 1} Λ)) h
    have : IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shAdj r).unit :=
      isIso_derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus_unit Λ r
    have : IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shAdj l).unit :=
      isIso_derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus_unit Λ l
    have (M : DerivedCategory.Plus (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
        IsIso (((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).exchange t l r b h.w).app
          M) :=
      isIso_of_isIso_plus_of_isZero Λ r _
        (isIso_map_mateEquiv_app_of_isIso ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).adj t)
          ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).adj b)
          ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shAdj r)
          ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shAdj l)
          (TwoSquare.mk _ _ _ _
            (inv ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).baseChange t l r b h.w)))
          M)
        (isZero_plus_upperStar_openImmersionLowerShriek Λ r _
          (by rw [r.range_closedComplement]; exact disjoint_compl_left) _)
        (isZero_plus_upperStar_lowerStar_openImmersionLowerShriek Λ isAddTorsion_of_finite h M)
    exact NatIso.isIso_of_isIso_app _

end Torsion

end Etale

end AlgebraicGeometry
