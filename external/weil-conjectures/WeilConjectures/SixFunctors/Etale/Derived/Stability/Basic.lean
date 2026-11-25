/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtaleFlat

/-!
# Stability of `Dctf`: pullback, tensor product and internal hom

Let `A` be a monoidal Grothendieck abelian coefficient category. This file proves that the
pullback `Lf^*` and the derived tensor product preserve the constructible finite-Tor categories
`Dctf(X, A)`, together with the shifts of the Tor amplitude, and reduces the internal hom
statements to the Verdier dual.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

omit [HasSmallSiteSheafify A] in
/-- Membership in `D_c^[a, b]` with Tor amplitude in `[a, b]` is invariant under
isomorphism. -/
lemma constructibleTorAmplitudeIn_of_iso {X : Scheme.{u}} {a b : ℤ}
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ K')
    (hK : constructibleTorAmplitudeIn A X a b K) : constructibleTorAmplitudeIn A X a b K' := by
  obtain ⟨⟨hbc, h₁, h₂⟩, hta⟩ := hK
  exact ⟨⟨(boundedConstructible A X).prop_of_iso e hbc,
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e b⟩,
    (torAmplitudeIn A X a b).prop_of_iso e hta⟩

/-! ### The exceptional inverse image -/

/-- For a finite étale `f`, the exceptional inverse image is the pullback, `Rf^! ≅ D(f^*)`:
`f` is proper, so `Rf_! ≅ Rf_*`; `f_*` is exact, so `Rf_* ≅ D(f_*)`; and `D(f_*) ⊣ D(f^*)`,
`f_*` being left adjoint to `f^*`
(`AlgebraicGeometry.Etale.lowerStarUpperStarAdjunctionOfIsFinite`). -/
noncomputable def rightDerivedUpperShriekIsoOfIsFiniteOfEtale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [_root_.AlgebraicGeometry.Etale f] [HasCompactification f] :
    R(f)^![Λ] ≅ D((f)^*[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedUpperShriekAdjunction Λ f).rightAdjointUniq
    ((Etale.lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} Λ)
        f).mapDerivedCategoryAdjunction.ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f ≪≫
        (f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorIsoMapDerivedCategory).symm)

/-! ### Stability of `Dctf` under the six operations -/

/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (i), constructibility: the pullback of a bounded constructible complex is bounded
constructible. -/
theorem boundedConstructible_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hbc : boundedConstructible A Y K) :
    boundedConstructible A X ((L((f)^*[A])).obj K) :=
  (boundedConstructible A X).prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory A f).app K).symm
    (hbc.mapDerivedCategory_upperStar f)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (i), amplitude: `Lf^*` preserves the Tor amplitude interval unchanged, the pullback of
a bounded flat model being a bounded flat model in the same degrees.

The pullback is assumed to preserve flat sheaves, which holds for every `f` under
`AlgebraicGeometry.Etale.UpperStarPreservesFlat A` (for instance for `A = ModuleCat Λ`), and for
every `A` when `f` is an open immersion or finite étale. This is no restriction: the statement for
`a = b = 0` and `K` a flat sheaf in degree `0` says exactly that `f^*` of a flat sheaf is flat. -/
theorem torAmplitudeIn_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(f)^*[A].PreservesFlat] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hta : torAmplitudeIn A Y a b K) :
    torAmplitudeIn A X a b ((L((f)^*[A])).obj K) := by
  -- `K` is represented by a complex `P` of flat sheaves in degrees `[a, b]`, so `Lf^* K` is
  -- represented by the complex `f^* P` of flat sheaves in degrees `[a, b]`
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hta
  refine (torAmplitudeIn A X a b).prop_of_iso
    (((f)^*[A].mapDerivedCategoryFactors.app P).symm ≪≫
      (f)^*[A].mapDerivedCategory.mapIso e ≪≫
      ((leftDerivedUpperStarIsoMapDerivedCategory A f).app K).symm)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b fun n ↦ ?_)
  exact Functor.PreservesFlat.flat_obj (F := (f)^*[A]) (hP n)

/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (i): `Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` is defined. -/
theorem constructibleFiniteTor_leftDerivedUpperStar [UpperStarPreservesFlat A] {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A Y K) :
    constructibleFiniteTor A X ((L((f)^*[A])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  exact ⟨boundedConstructible_leftDerivedUpperStar A f hbc,
    a, b, torAmplitudeIn_leftDerivedUpperStar A f a b hta⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation for the exceptional inverse
image.

Clause (i), finite étale case: for a finite étale `f`, `Rf^!` preserves the constructible
interval and the Tor amplitude *unchanged*, `Rf^! ≅ D(f^*)` being exact and `f^*` preserving
flat sheaves. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isFinite_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [_root_.AlgebraicGeometry.Etale f]
    [HasCompactification f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b ((R(f)^![Λ]).obj K) := by
  obtain ⟨⟨hbc, hab⟩, hta⟩ := hK
  refine constructibleTorAmplitudeIn_of_iso _
    ((rightDerivedUpperShriekIsoOfIsFiniteOfEtale Λ f).app K).symm ⟨⟨?_,
      ((f)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab⟩, ?_⟩
  · exact hbc.mapDerivedCategory_upperStar f
  · exact (torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ f a b hta)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (ii), amplitude: Tor amplitudes add under the derived tensor product,
`[a, b], [c, d] ↦ [a + c, b + d]`. This is blueprint `proposition-six-operations-dctf--14` (ii), Tor
amplitude. -/
theorem torAmplitudeIn_tensor (X : Scheme.{u}) (a b c d : ℤ)
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hKt : torAmplitudeIn A X a b K) (hMt : torAmplitudeIn A X c d M) :
    torAmplitudeIn A X (a + c) (b + d) (((-⊗ᴸ-(X)[A]).obj K).obj M) :=
  _root_.DerivedCategory.torAmplitudeIn_tensor hKt hMt

omit [HasSmallSiteSheafify A] in
/-- The derived tensor product of a bounded complex with a complex of finite Tor amplitude is
bounded. -/
theorem bounded_derivedTensor_of_finiteTorAmplitude (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : _root_.DerivedCategory.TStructure.t.bounded K) (hMt : finiteTorAmplitude A X M) :
    _root_.DerivedCategory.TStructure.t.bounded (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  obtain ⟨a, b, hab⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hK
  obtain ⟨c, d, hcd⟩ := hMt
  exact (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
    ⟨_, _, _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right hab hcd⟩

/-- **Dévissage for the derived tensor product.** Suppose that constructible sheaves are closed
under kernels, cokernels and extensions, and that the homology sheaves of `F[0] ⊗ᴸ G[0]` are
constructible for constructible sheaves `F` and `G`. Then the derived tensor product of two
bounded complexes with constructible homology has constructible homology. -/
theorem constructibleHomology_derivedTensor [PreservesFiniteLimits (CategoryTheory.forget A)]
    {X : Scheme.{u}} [(Etale.constructibleSheaf A X).IsClosedUnderKernels]
    [(Etale.constructibleSheaf A X).IsClosedUnderCokernels]
    [(Etale.constructibleSheaf A X).IsClosedUnderExtensions]
    (hTor : ∀ F G : Sheaf X.smallEtaleTopology A, Etale.constructibleSheaf A X F →
      Etale.constructibleSheaf A X G → ∀ n : ℤ, Etale.constructibleSheaf A X
        ((_root_.DerivedCategory.homologyFunctor _ n).obj
          (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))))
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : boundedConstructible A X K) (hM : boundedConstructible A X M) :
    constructibleHomology A X (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  rw [constructibleHomology_eq]
  have : (_root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)).IsTriangulated :=
    inferInstance
  -- first for `K` a constructible sheaf in degree `0`
  have h₀ (F : Sheaf X.smallEtaleTopology A) (hF : Etale.constructibleSheaf A X F) :
      _root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)
        (((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj M) :=
    letI := _root_.DerivedCategory.commShiftTensorLeft
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    have : ((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology A) 0).obj F)).IsTriangulated :=
      _root_.DerivedCategory.isTriangulated_tensorLeft
        (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    _root_.DerivedCategory.prop_of_bounded
      ((_root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)).inverseImage
        ((-⊗ᴸ-(X)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
      (Etale.constructibleSheaf A X) (fun G hG n ↦ hTor F G hF hG n) M hM.1 hM.2
  let := _root_.DerivedCategory.commShiftTensorRight (K := M)
  have : ((-⊗ᴸ-(X)[A]).flip.obj M).IsTriangulated :=
    _root_.DerivedCategory.isTriangulated_tensorRight (K := M)
  exact _root_.DerivedCategory.prop_of_bounded
    ((_root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X)).inverseImage
      ((-⊗ᴸ-(X)[A]).flip.obj M))
    (Etale.constructibleSheaf A X) h₀ K hK.1 hK.2

omit [HasSmallSiteSheafify A] in
/-- If `K` is dualizable of Tor amplitude in `[a, b]` and `M` has Tor amplitude in `[c, d]`,
then `RHom(K, M) ≅ K^∨ ⊗ᴸ M` has Tor amplitude in `[c - b, d - a]`, the dual `K^∨` having Tor
amplitude in `[-b, -a]`
(`DerivedCategory.torAmplitudeIn_of_exactPairing`). -/
theorem torAmplitudeIn_derivedHom_of_isDualizable_aux {X : Scheme.{u}} {a b c d : ℤ}
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hKt : torAmplitudeIn A X a b K) (hKd : IsDualizable K) (hMt : torAmplitudeIn A X c d M) :
    torAmplitudeIn A X (c - b) (d - a) (((RHom(X)[A]).obj (op K)).obj M) := by
  -- `RHom(K, M) ≅ K^∨ ⊗ᴸ M`, and the dual `K^∨` has Tor amplitude in `[-b, -a]`
  obtain ⟨_⟩ := hKd
  obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor (isDualizable_of_hasRightDual K) M
  have hd := _root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt
  have h := _root_.DerivedCategory.torAmplitudeIn_tensor hd hMt
  refine (torAmplitudeIn A X _ _).prop_of_iso
    (whiskerRightIso (coefficientDualIsoOfExactPairing Kᘁ K).symm M ≪≫ e) ?_
  rw [show c - b = -b + c by omega, show d - a = -a + d by omega]
  exact h

/-! ### Internal hom: reductions -/

section DerivedHomReductions

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

omit [HasSmallSiteSheafify A] in
/-- **Restriction to an open commutes with the internal hom**, `j^* RHom(K, N) ≅
RHom(j^* K, j^* N)`: the two sides are right adjoint to `G ↦ K ⊗ᴸ j_! G` and to
`G ↦ j_!(j^* K ⊗ᴸ G)`, which agree by the projection formula for `j_!` (and the symmetry of the
derived tensor product). -/
theorem nonempty_iso_mapDerivedCategory_upperStar_derivedHom {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale.UpperStarPreservesFlat A]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (K N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty (D((j)^*[A]).obj ((RHom(X)[A].obj (op K)).obj N) ≅
      (RHom(U)[A].obj (op (D((j)^*[A]).obj K))).obj (D((j)^*[A]).obj N)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf X.smallEtaleTopology A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf U.smallEtaleTopology A)
  let adj₁ := (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).comp
    (derivedTensorHomAdjunction A K)
  let adj₂ := (derivedTensorHomAdjunction A (D((j)^*[A]).obj K)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
  let e : D((j)_!open[A]) ⋙ (-⊗ᴸ-(X)[A]).obj K ≅
      (-⊗ᴸ-(U)[A]).obj (D((j)^*[A]).obj K) ⋙ D((j)_!open[A]) :=
    Functor.isoWhiskerLeft _ (BraidedCategory.tensorLeftIsoTensorRight K) ≪≫
      (((flipFunctor _ _ _).mapIso
        (derivedOpenImmersionLowerShriekProjectionIso (FC := FC) A j)).app K).symm ≪≫
      Functor.isoWhiskerRight ((curriedTensor _).flip.mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory A j).app K) ≪≫
          (BraidedCategory.tensorLeftIsoTensorRight _).symm) D((j)_!open[A])
  exact ⟨((adj₁.ofNatIsoLeft e).rightAdjointUniq adj₂).app N⟩

end DerivedHomReductions

/-- If `M` is reflexive for the Verdier dual, `RHom(K, M) ≅ 𝔻(𝔻M ⊗ᴸ K)`: currying
`RHom(𝔻M ⊗ᴸ K, ω) ≅ RHom(K, RHom(𝔻M, ω))`. -/
theorem nonempty_iso_derivedHom_verdierDual {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a]
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : M ≅ (verdierDual Λ a).obj (op ((verdierDual Λ a).obj (op M)))) :
    Nonempty ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M ≅
      (verdierDual Λ a).obj (op ((verdierDual Λ a).obj (op M) ⊗ K))) := by
  let N := (verdierDual Λ a).obj (op M)
  exact ⟨(RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).mapIso e ≪≫
    ((((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) (N ⊗ K)).ofNatIsoLeft
        (tensorLeftTensor N K)).rightAdjointUniq
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).comp
        (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) N))).app
        (dualizingComplex Λ a)).symm⟩

/-- If the Verdier dual relative to `a` preserves `Dctf(X, Λ)` and is reflexive on it, and the
derived tensor product preserves `Dctf(X, Λ)`, so does the internal hom. -/
theorem constructibleFiniteTor_derivedHom_of_verdierDual {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a]
    (hD : ∀ {N}, constructibleFiniteTor (ModuleCat.{u + 1} Λ) X N →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((verdierDual Λ a).obj (op N)))
    (hbid : ∀ {N}, constructibleFiniteTor (ModuleCat.{u + 1} Λ) X N →
      Nonempty (N ≅ (verdierDual Λ a).obj (op ((verdierDual Λ a).obj (op N)))))
    (htens : ∀ {K M}, constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M))
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M) := by
  obtain ⟨e⟩ := hbid hM
  obtain ⟨e'⟩ := nonempty_iso_derivedHom_verdierDual Λ a K M e
  obtain ⟨hbc, c, d, hcd⟩ := hD (htens (hD hM) hK)
  exact ⟨(boundedConstructible (ModuleCat.{u + 1} Λ) X).prop_of_iso e'.symm hbc, c, d,
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d).prop_of_iso e'.symm hcd⟩

end Etale

end AlgebraicGeometry
