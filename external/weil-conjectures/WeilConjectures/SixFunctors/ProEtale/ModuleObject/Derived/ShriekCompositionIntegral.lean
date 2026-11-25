/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition

/-!

# Composition of the derived lower shriek on bounded constructible `𝒪_E`-complexes

For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with ring of integers `𝒪_E` and composable morphisms
`f : X ⟶ Y`, `g : Y ⟶ S` of separated `k`-schemes of finite type, this file gives the
composition isomorphism
```
R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!
```
on bounded constructible `𝒪_E`-complexes
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicIntegers`). The construction is
that of `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp` for the coefficients `E̲`,
with the integral inputs of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral`
(independence of the compactification, which rests on proper base change for `𝒪_E`-sheaves),
and the interchange of proper direct image with extension by zero for `𝒪_E`-sheaves
(`isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers`), deduced
here from proper base change for `𝒪_E`-sheaves by the argument of
`isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_of_isIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` (`𝒪_E`-coefficient) is the exchange
morphism `CategoryTheory.Adjunction.exchangeRight` of the extension-by-zero base-change
isomorphism under the adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers_eq
    (sq : IsPullback p i' j p') :
    PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sq =
      Adjunction.exchangeRight
        (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
          (Profinite.padicIntegersRingObj ℓ E) ℓ sq) := by
  unfold PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep
    PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep
    Adjunction.exchangeRight
  rfl

/-- **Interchanging proper direct image and extension by zero** for bounded constructible
`𝒪_E`-sheaves: the exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'`
proper is an isomorphism. The argument is that of
`isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_of_isIso`: over the open `X`
it follows from the mate calculus and proper base change for `𝒪_E`-sheaves
(`isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers`), and over the closed complement
of `X` both sides vanish. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers
    [IsProper p'.left] (sq : IsPullback p i' j p') :
    IsIso (PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ℓ E sq) := by
  have : QuasiCompact (j.left ≫ Z.hom) := by
    rw [Over.w j]
    infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left Z.hom
  have h₁ := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E sq.flip
  have h₂ := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E
    (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j))
  have hK (K : Dᵇc(X'.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
      IsIso ((PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        ℓ E sq).app K) := by
    refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl
      (Profinite.padicIntegersRingObj ℓ E) ℓ (overClosedComplement j) j
      (isCompl_range_overClosedComplement j) _ ?_ ?_
    · -- Over the open `X`, by the mate calculus and proper base change.
      rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers_eq]
      have : IsIso ((Adjunction.exchangeRight
          (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
          (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
          (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
            sq.toCommSq.flip)).app
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ
              i').obj K)) := by
        rw [← PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
        infer_instance
      exact Adjunction.isIso_map_exchangeRight_app
        (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicIntegersRingObj ℓ E) ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicIntegersRingObj ℓ E) ℓ i') _ _
        (boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft
          (Profinite.padicIntegersRingObj ℓ E) ℓ sq.toCommSq) K
    · -- Over the closed complement both sides vanish.
      have hS : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
          (overClosedComplement j)).obj
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ
            j).obj ((PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p).obj K))) :=
        isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
          (Profinite.padicIntegersRingObj ℓ E) ℓ j (overClosedComplement j)
          (isCompl_range_overClosedComplement j).disjoint.symm _
      have := Functor.preservesZeroMorphisms_of_isRightAdjoint
        (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E
          (overPullbackSnd p' (overClosedComplement j)))
      have hT : IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
          (overClosedComplement j)).obj
          ((PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p').obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ
              i').obj K))) :=
        ((PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E
          (overPullbackSnd p' (overClosedComplement j))).map_isZero
          (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
            (Profinite.padicIntegersRingObj ℓ E) ℓ i'
            (overPullbackFst p' (overClosedComplement j))
            (disjoint_range_overPullbackFst_overClosedComplement sq.toCommSq) K)).of_iso
          (asIso ((PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E
            (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j)).toCommSq).app
              ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E)
                ℓ i').obj K)))
      exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
  exact NatIso.isIso_of_isIso_app _

end Exchange

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `𝒪_E`-sheaves, constructed as `boundedConstructibleLowerShriekComp`: for
the chosen compactifications `c` of `f` and `c'` of `g` and a compactification `d` of `p ≫ j`
with cartesian square, it chains the independence of the compactification, the composition
isomorphisms of extension by zero and of `Rf_*`, and the inverse of the exchange isomorphism
`Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp_padicIntegers :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E (f ≫ g) ≅
      PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g :=
  let c := compactificationOverField f
  let c' := compactificationOverField g
  have hd := Compactification.exists_isPullback_overG_overI c c'
  let d := hd.choose
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers ℓ E
    sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers ℓ E
    hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E _ (c.overComp c' d) ≪≫
    (PadicIntegersRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _
      (PadicIntegersRingObj.boundedConstructibleLowerStarComp ℓ E d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso
        (PadicIntegersRingObj.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
          ℓ E hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
