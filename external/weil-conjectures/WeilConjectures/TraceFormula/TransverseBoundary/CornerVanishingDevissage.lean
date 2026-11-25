/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.Grp.Biproducts
public import WeilConjectures.SixFunctors.Etale.Derived.ForgetCohomologyVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.StrictLocalizationVanishing
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Forget
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerConnected
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerVanishingConstant
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyDevissage
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyPullback

/-!
# Vanishing at the transverse corner, assuming the constant case

Let `S` be the strict localization of the surface of a transverse corner at a geometric point
`z̄` (with algebraically closed field), `i' : S - (X_S ∪ Y_S) ⟶ S - Y_S` and
`p' : S - (X_S ∪ Y_S) ⟶ Z - (X ∪ Y)`. Assuming that the restriction maps
`H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` are bijective (blueprint
`lemma-punctured-surface-punctured-curve--1`), this file proves that `(Rj_* i_! E)_z̄ = 0` for every
bounded `E` with finite `ℓ`-group monodromy (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`):

* *constant coefficients*: `RΓ(S - Y_S, i'_! N) = 0` for a finite `Λ`-module `N` killed by `ℓ`,
  as an abelian sheaf a finite sum of copies of `ℤ/ℓ`;
* *dévissage* on the connected `S - (X_S ∪ Y_S)`
  (`AlgebraicGeometry.Etale.prop_singleFunctor_of_hasFiniteEllGroupMonodromy`) gives
  `RΓ(S - Y_S, i'_! p'^* H) = 0` for every sheaf `H` with finite `ℓ`-group monodromy;
* *stalk formula*: `(R^q j_* i_! H)_z̄ = H^q(S - Y_S, (i_! H)|) = H^q(S - Y_S, i'_! p'^* H)`
  (`Etale.isZero_leftDerivedUpperStar_rightDerivedLowerStar_of_subsingleton_sheafH`
  and base change of the extension by zero);
* *dévissage* of the bounded complex `E` by truncation.

## Main statements

- `TransverseCorner.isZero_leftDerivedUpperStar_boundaryComplex_of_bijective`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k) {ℓ : ℕ} [Fact ℓ.Prime]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (zbar : Spec (.of Ω) ⟶ C.Z)

/-- The property of `K ∈ D(S - (X_S ∪ Y_S), Λ)` that `RΓ(S - Y_S, i'_! K) = 0`, to which the
dévissage is applied (blueprint `lemma-cohomology-near-two-transverse-divisors--1`). -/
def IsAcyclicExtension :
    ObjectProperty (DerivedCategory
      (Sheaf (C.strictLocalizationComplement zbar).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ IsZero ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
    (pullback C.j (strictLocalizationToBase zbar))).obj
      ((D((C.strictLocalizationComplementι zbar)_!open[ModuleCat.{u + 1} Λ])).obj K))

instance : (C.IsAcyclicExtension Λ zbar).IsClosedUnderIsomorphisms where
  of_iso e h := h.of_iso
    ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).mapIso
      ((D((C.strictLocalizationComplementι zbar)_!open[ModuleCat.{u + 1} Λ])).mapIso e)).symm

omit [Finite Λ] in
/-- `IsAcyclicExtension` is stable under shifts. -/
lemma isAcyclicExtension_shift
    (K : DerivedCategory
      (Sheaf (C.strictLocalizationComplement zbar).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (hK : C.IsAcyclicExtension Λ zbar K) : C.IsAcyclicExtension Λ zbar (K⟦n⟧) :=
  ((shiftFunctor _ n).map_isZero hK).of_iso
    (((D((C.strictLocalizationComplementι zbar)_!open[ModuleCat.{u + 1} Λ]) ⋙
      Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).commShiftIso n).app K)

omit [Finite Λ] in
/-- `IsAcyclicExtension` is stable under extensions. -/
lemma isAcyclicExtension_ext (T : Pretriangulated.Triangle (DerivedCategory
      (Sheaf (C.strictLocalizationComplement zbar).smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _) (h₁ : C.IsAcyclicExtension Λ zbar T.obj₁)
    (h₃ : C.IsAcyclicExtension Λ zbar T.obj₃) : C.IsAcyclicExtension Λ zbar T.obj₂ :=
  have : (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
      (pullback C.j (strictLocalizationToBase zbar))).IsTriangulated :=
    inferInstanceAs ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated)
  Pretriangulated.Triangle.isZero₂_of_isZero₁₃ _
    ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map_distinguished _
      ((D((C.strictLocalizationComplementι zbar)_!open[ModuleCat.{u + 1} Λ])).map_distinguished
        T hT)) h₁ h₃

omit [Finite Λ] in
/-- Constant coefficients (blueprint `lemma-cohomology-near-two-transverse-divisors--1`): if the
restriction maps `H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` are bijective, then
`RΓ(S - Y_S, i'_! N) = 0` for every finite `Λ`-module `N` killed by `ℓ`. -/
lemma isAcyclicExtension_constantSheaf
    (hbij : ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap
      (pullback.snd (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar)))
      ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ) q))
    (N : ModuleCat.{u + 1} Λ) (hN : Finite N) (hℓN : ∀ n : N, (ℓ : Λ) • n = 0) :
    C.IsAcyclicExtension Λ zbar ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (C.strictLocalizationComplement zbar).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj N)) := by
  refine IsZero.of_iso ?_ ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).mapIso
    ((Functor.mapDerivedCategorySingleFunctor
      (C.strictLocalizationComplementι zbar)_!open[ModuleCat.{u + 1} Λ] 0).app _))
  refine (Etale.isZero_rightDerivedGlobalSections_singleFunctor_iff _ _).2 fun q ↦ ?_
  let Φ : AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    constantSheaf (C.strictLocalizationComplement zbar).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (C.strictLocalizationComplementι zbar)_!open[AddCommGrpCat.{u + 1}] ⋙
        Sheaf.functorH _ q
  have h₀ : IsZero (Φ.obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) := by
    have := C.subsingleton_sheafH_strictLocalizationComplement zbar ℓ hbij q
    exact (@AddCommGrpCat.isZero_of_subsingleton _ this).of_iso ((Sheaf.functorH _ q).mapIso
      (((C.strictLocalizationComplementι zbar)_!open[AddCommGrpCat.{u + 1}]).mapIso
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (C.strictLocalizationComplementι zbar)).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))))).symm
  have h := AddCommGrpCat.isZero_obj_of_nsmul_eq_zero Φ h₀
    ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj N) fun (n : N) ↦
      (Nat.cast_smul_eq_nsmul Λ ℓ (n : N)).symm.trans (hℓN n)
  refine (AddCommGrpCat.subsingleton_of_isZero (h.of_iso ((Sheaf.functorH _ q).mapIso
    ((Etale.openImmersionLowerShriekSheafForget₂Iso Λ _).app _ ≪≫
      ((C.strictLocalizationComplementι zbar)_!open[AddCommGrpCat.{u + 1}]).mapIso
        ((Etale.constantSheafSheafComposeForget₂Iso Λ).app N)))))

/-- Sheaves (blueprint `lemma-cohomology-near-two-transverse-divisors--1`): for a sheaf `H` on
`Z - (X ∪ Y)` with finite `ℓ`-group monodromy, the stalk at `z̄` of `Rj_* i_! H` vanishes. -/
lemma isZero_leftDerivedUpperStar_rightDerivedLowerStar_singleFunctor
    (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (hbij : ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap
      (pullback.snd (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar)))
      ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ) q))
    (H : Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : Etale.HasFiniteEllGroupMonodromy ℓ H) :
    IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj ((R((C.j)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((C.i)_!open[ModuleCat.{u + 1} Λ].obj H)))) := by
  refine Etale.isZero_leftDerivedUpperStar_rightDerivedLowerStar_of_subsingleton_sheafH C.j zbar _
    fun q ↦ ?_
  have hsq := C.isPullback_strictLocalizationComplement zbar
  have := Etale.isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) hsq
  let G := (C.strictLocalizationComplementToV zbar)^*[ModuleCat.{u + 1} Λ].obj H
  have hG : C.IsAcyclicExtension Λ zbar ((DerivedCategory.singleFunctor _ 0).obj G) := by
    rcases isEmpty_or_nonempty (C.strictLocalizationComplement zbar) with hV | hV
    · exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
        (Scheme.Etale.isZero_sheaf_of_isEmpty G)))
    · have : ConnectedSpace (C.strictLocalizationComplement zbar) :=
        { toPreconnectedSpace := C.preconnectedSpace_strictLocalizationComplement zbar
          toNonempty := hV }
      exact Etale.prop_singleFunctor_of_hasFiniteEllGroupMonodromy ℓ hΛ _
        (C.isAcyclicExtension_ext Λ zbar)
        (fun N hN hℓN ↦ C.isAcyclicExtension_constantSheaf Λ zbar hbij N hN hℓN) G
        (hH.upperStar _)
  have hq := (Etale.isZero_rightDerivedGlobalSections_singleFunctor_iff _ _).1
    (hG.of_iso ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).mapIso
      ((Functor.mapDerivedCategorySingleFunctor
        (C.strictLocalizationComplementι zbar)_!open[ModuleCat.{u + 1} Λ] 0).app G).symm)) q
  exact AddCommGrpCat.subsingleton_of_isZero ((@AddCommGrpCat.isZero_of_subsingleton _ hq).of_iso
    ((Sheaf.functorH _ q).mapIso ((Etale.sheafForget₂ Λ _).mapIso
      (asIso ((Etale.openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
        hsq.toCommSq).app H)).symm)))

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`, assuming
`lemma-punctured-surface-punctured-curve--1` in the form of the bijectivity of the restriction maps
`H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)`: for a geometric point `z̄` with algebraically closed
field, the stalk at `z̄` of `M = Rj_* i_! E` vanishes for every bounded `E` with finite `ℓ`-group
monodromy. -/
theorem isZero_leftDerivedUpperStar_boundaryComplex_of_bijective
    (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (hbij : ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap
      (pullback.snd (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar)))
      ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ) q))
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) :
    IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E)) := by
  let Φ := D((C.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ R((C.j)_*[ModuleCat.{u + 1} Λ]) ⋙
    L((zbar)^*[ModuleCat.{u + 1} Λ])
  let Q : ObjectProperty (DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    fun K ↦ IsZero (Φ.obj K)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.of_iso (Φ.mapIso e).symm⟩
  obtain ⟨⟨a, b, ha, hb⟩, hE⟩ := hE
  refine DerivedCategory.prop_of_bounded_of_degreewise Q (fun K hK ↦ Φ.map_isZero hK)
    (fun T hT h₁ h₃ ↦ Pretriangulated.Triangle.isZero₂_of_isZero₁₃ _
      ((L((zbar)^*[ModuleCat.{u + 1} Λ])).map_distinguished _
        ((R((C.j)_*[ModuleCat.{u + 1} Λ])).map_distinguished _
          ((D((C.i)_!open[ModuleCat.{u + 1} Λ])).map_distinguished T hT))) h₁ h₃)
    (fun _ ↦ Etale.HasFiniteEllGroupMonodromy ℓ) (fun q H hH ↦ ?_) E ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hE
  have h₀ : Q ((DerivedCategory.singleFunctor _ 0).obj H) :=
    (C.isZero_leftDerivedUpperStar_rightDerivedLowerStar_singleFunctor Λ zbar hΛ hbij H hH).of_iso
      ((R((C.j)_*[ModuleCat.{u + 1} Λ]) ⋙ L((zbar)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((((C.i)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app H))
  exact Q.prop_of_iso (((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by lia)).app H)
    (((shiftFunctor _ (-q)).map_isZero h₀).of_iso ((Φ.commShiftIso (-q)).app _))

end AlgebraicGeometry.Scheme.TransverseCorner
