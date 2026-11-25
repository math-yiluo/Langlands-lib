/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.ModuleCat
public import WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableBounded
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual

/-!
# Objects of `Dctf(X, Λ)` are compact in `D(X_ét, Λ)`

Blueprint `proposition-compactness-finite-coefficients`. Let `k` be a field of finite cohomological
dimension for `Λ`-modules, `X` a finite-type `k`-scheme and `Λ` a finite ring whose exponent is
invertible on `X`. Every object `C` of `Dctf(X_ét, Λ)` is compact in `D(X_ét, Λ)`, and has *bounded
morphisms*: `Hom(C, G) = 0` for `G` in sufficiently negative degrees
(`AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor`).

The proof follows the blueprint. Both properties are stable under shifts, extensions and
retracts (`DerivedCategory.compactBoundedHom`), and are transported along left adjoints whose
right adjoints preserve coproducts and have bounded amplitude
(`DerivedCategory.compactBoundedHom_of_adjunction`). By the dévissage
`AlgebraicGeometry.Etale.constructibleFiniteTor_eq_triangEnvelope_ctfGenerators` it suffices to
treat the generators `Rg_* j_! L`. Starting from `Λ[0]` in `D(Λ)`, one applies successively:

* the constant sheaf functor at the point `Spec k`, right adjoint `RΓ(Spec k, -)` of finite
  cohomological dimension;
* the pullback along `S ⟶ Spec k`, right adjoint the direct image of finite cohomological
  dimension;
* the tensor product with the lisse flat sheaf `L`, right adjoint the tensor product with its
  dual;
* the extension by zero along the open immersion `j`, right adjoint the exact restriction;
* the direct image along the closed immersion `g`, right adjoint `Rg^!`
  (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedFunctor_closedUpperShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme _root_.DerivedCategory

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The object `Λ[0]` of `D(Λ)` is compact with bounded morphisms. -/
lemma compactBoundedHom_singleFunctor_self :
    compactBoundedHom (ModuleCat.{u + 1} Λ)
      ((singleFunctor (ModuleCat.{u + 1} Λ) 0).obj (ModuleCat.of Λ Λ)) := by
  refine ⟨isCompactObj_singleFunctor_obj_self, -1, fun G hG f ↦ ?_⟩
  apply (singleFunctorZeroHomEquiv (ModuleCat.of Λ Λ) G).injective
  exact (isZero_of_isLE G (-1) 0 (by lia)).eq_of_tgt _ _

/-- On a quasi-compact quasi-separated scheme of finite cohomological dimension, the constant
sheaf `Λ` placed in degree `0` is compact with bounded morphisms in `D(X_ét, Λ)`: it is the
image of `Λ[0]` under the left adjoint of `RΓ(X, -)`. -/
lemma compactBoundedHom_singleFunctor_constantSheaf (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (hX : HasFiniteCohomologicalDimension Λ X) :
    compactBoundedHom (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      ((singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))) := by
  let adj := (constantSheafΓAdj X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).mapDerivedCategoryRightDerivedAdjunction
  have : ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor :=
    preservesCoproducts_rightDerivedGlobalSections Λ X hX
  obtain ⟨d, hd⟩ := hX
  have hcd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d.toNat < q →
      IsZero (((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q).obj F) :=
    fun F q hq ↦
    Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia))
  exact (compactBoundedHom _).prop_of_iso
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategorySingleFunctor
      0).app (ModuleCat.of Λ Λ))
    (compactBoundedHom_of_adjunction adj d.toNat
      (fun Y n _ ↦ Functor.isLE_rightDerivedFunctor_obj _ d.toNat hcd Y n)
      (compactBoundedHom_singleFunctor_self Λ))

/-- At a field of finite cohomological dimension, the unit `Λ` of `D((Spec k)_ét, Λ)` is compact
with bounded morphisms. -/
lemma compactBoundedHom_unit_spec {k : Type u} [Field k]
    (hk : HasFiniteCohomologicalDimension Λ (Spec (.of k))) :
    compactBoundedHom (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (𝟙_ (_root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)))) :=
  (compactBoundedHom _).prop_of_iso ((singleFunctor _ 0).mapIso (Iso.refl _) ≪≫
      singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) (Spec (.of k)))
    (compactBoundedHom_singleFunctor_constantSheaf Λ (Spec (.of k)) hk)

/-- On a scheme of finite type over a field of finite cohomological dimension, the unit `Λ` of
`D(S_ét, Λ)` is compact with bounded morphisms: it is the pullback of the unit at the point,
and the direct image to the point has finite cohomological dimension. -/
lemma compactBoundedHom_unit_of_finiteType (hΛ : IsAddTorsion Λ) {k : Type u} [Field k]
    (hk : HasFiniteCohomologicalDimension Λ (Spec (.of k))) {S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] [QuasiSeparated aS] :
    compactBoundedHom (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (𝟙_ (_root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))) := by
  have hcd' := hasFiniteCohomologicalDimensionMorphism Λ hΛ aS (𝟙 _) aS (Category.comp_id _)
  have := preservesCoproducts_rightDerivedLowerStar Λ aS hcd'
  obtain ⟨d, hd⟩ := hcd'
  have hcd : ∀ (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d.toNat < q →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} Λ) aS).rightDerived q).obj F) :=
    fun F q hq ↦
    Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia))
  exact (compactBoundedHom _).prop_of_iso (leftDerivedUpperStarUnitIso _ aS)
    (compactBoundedHom_of_adjunction (derivedUpperStarLowerStarAdjunction _ aS) d.toNat
      (fun Y n _ ↦ Functor.isLE_rightDerivedFunctor_obj _ d.toNat hcd Y n)
      (compactBoundedHom_unit_spec Λ hk))

/-- A finite locally constant flat sheaf is dualizable. -/
lemma isDualizable_of_isFiniteLocallyConstantSheaf [Finite Λ] {S : Scheme.{u}}
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf L]
    (hL : ObjectProperty.flat L) : IsDualizable L := by
  let := exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf L hL
  exact ⟨@HasRightDual.mk _ _ _ _ ((ihom L).obj (𝟙_ _)) (BraidedCategory.exactPairing_swap _ _)⟩

/-- If the unit of `D(S_ét, Λ)` is compact with bounded morphisms, so is every finite locally
constant flat sheaf `L` placed in degree `0`: it is the image of the unit under `L ⊗ -`, whose
right adjoint `L^∨ ⊗ -` preserves coproducts (being also a left adjoint) and degrees. -/
lemma compactBoundedHom_singleFunctor_of_isFiniteLocallyConstantSheaf [Finite Λ] {S : Scheme.{u}}
    (hS : compactBoundedHom (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (𝟙_ (_root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))))
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf L]
    (hL : ObjectProperty.flat L) :
    compactBoundedHom (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      ((singleFunctor _ 0).obj L) := by
  let P := (HomologicalComplex.single (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (.up ℤ) 0).obj L
  have hP (n : ℤ) : IsDualizable (P.X n) := by
    by_cases h : n = 0
    · subst h
      exact (isDualizable_of_isFiniteLocallyConstantSheaf Λ L hL).of_iso
        (HomologicalComplex.singleObjXSelf _ _ _).symm
    · have hz : IsZero (P.X n) := HomologicalComplex.isZero_single_obj_X _ _ _ _ h
      have : IsFiniteLocallyConstantSheaf (0 : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
        IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _)
      exact (isDualizable_of_isFiniteLocallyConstantSheaf Λ _
        (ObjectProperty.flat_of_isZero (isZero_zero _))).of_iso (hz.isoZero).symm
  obtain ⟨Y, hpair, hY⟩ := exists_exactPairing_Q_obj P 0 0 hP
  let := DerivedCategory.braidedCategory' (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let _ := BraidedCategory.exactPairing_swap (Q.obj P) Y
  let adj : tensorLeft (Q.obj P) ⊣ tensorLeft Y := tensorLeftAdjunction Y (Q.obj P)
  have : ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) (tensorLeft Y) := fun J ↦
    (tensorLeftAdjunction (Q.obj P) Y).leftAdjoint_preservesColimits.1
  have : Y.IsLE 0 := by simpa using hY
  refine (compactBoundedHom _).prop_of_iso (ρ_ (Q.obj P) ≪≫
    ((singleFunctorIsoCompQ _ 0).app L).symm) (compactBoundedHom_of_adjunction adj 0
      (fun N n _ ↦ ?_) hS)
  simpa using isLE_tensor Y N 0 n

/-- The extension by zero along an open immersion preserves compact objects with bounded
morphisms: its right adjoint, the restriction, is exact and preserves coproducts. -/
lemma compactBoundedHom_mapDerivedCategory_openImmersionLowerShriek {U Y : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j]
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : compactBoundedHom _ K) :
    compactBoundedHom _ ((j)_!open[ModuleCat.{u + 1} Λ].mapDerivedCategory.obj K) := by
  have : ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) (j)^*[ModuleCat.{u + 1} Λ] :=
    fun J ↦ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).leftAdjoint_preservesColimits.1
  exact compactBoundedHom_of_adjunction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j) 0
    (fun N n _ ↦ by simpa using ((j)^*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj N n) hK

/-- The direct image along a closed immersion into a finite-type scheme over a field preserves
compact objects with bounded morphisms: its right adjoint `Rg^!` preserves coproducts and has
bounded amplitude, the complementary open immersion having finite cohomological dimension. -/
lemma compactBoundedHom_rightDerivedLowerStar_of_isClosedImmersion (hΛ : IsAddTorsion Λ)
    {k : Type u} [Field k] {Z X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] (g : Z ⟶ X) [IsClosedImmersion g]
    {K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : compactBoundedHom _ K) :
    compactBoundedHom _ (((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.obj K) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  let V : X.Opens := ⟨(Set.range g.base)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : Set.range g.base = (Set.range V.ι.base)ᶜ := by
    simp [V, Scheme.Opens.range_ι]
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hV := hasFiniteCohomologicalDimensionMorphism Λ hΛ (V.ι ≫ aX) aX V.ι rfl
  have := preservesColimitsOfShape_rightDerivedFunctor_closedUpperShriek g V.ι hij hV
  obtain ⟨c, hc⟩ := exists_isLE_rightDerivedFunctor_closedUpperShriek g V.ι hij hV
  exact compactBoundedHom_of_adjunction (derivedLowerStarClosedUpperShriekAdjunction g V.ι hij) c
    (fun N n hN ↦ hc N n hN) hK

/-- Blueprint `proposition-compactness-finite-coefficients`: on a finite-type scheme `X` over a
field `k` of finite cohomological dimension, every object of `Dctf(X_ét, Λ)` is compact in
`D(X_ét, Λ)` and has bounded morphisms, for a finite ring `Λ` whose exponent is invertible on
`X`. -/
theorem compactBoundedHom_of_constructibleFiniteTor [Finite Λ] {k : Type u} [Field k]
    (hk : HasFiniteCohomologicalDimension Λ (Spec (.of k))) {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
    [HasInvertibleExponent Λ X]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    compactBoundedHom _ K := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  rw [constructibleFiniteTor_eq_triangEnvelope_ctfGenerators Λ aX] at hK
  refine (ObjectProperty.triangEnvelope_le_iff (ctfGenerators Λ X)).2 ?_ K hK
  rintro K ⟨str, i, Ubar, j, _, g, _, -, -, L, _, hL, ⟨e⟩⟩
  have : TopologicalSpace.NoetherianSpace (str.domain i) :=
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
    have : IsNoetherian X := {}
    (str.immersion i).isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have h₁ := compactBoundedHom_unit_of_finiteType Λ hΛ hk (j ≫ g ≫ aX)
  have h₂ := compactBoundedHom_singleFunctor_of_isFiniteLocallyConstantSheaf Λ h₁ L hL
  have h₃ := compactBoundedHom_mapDerivedCategory_openImmersionLowerShriek Λ j h₂
  exact (compactBoundedHom _).prop_of_iso e.symm
    (compactBoundedHom_rightDerivedLowerStar_of_isClosedImmersion Λ hΛ aX g h₃)

end Etale

end AlgebraicGeometry
