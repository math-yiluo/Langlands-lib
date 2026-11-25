/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Stability of `Dctf` under the internal hom

For a finite coefficient ring `Λ` whose exponent is invertible on schemes of finite type over an
algebraically closed field `k`, the internal hom `RHom(K, M)` of two objects of `Dctf` lies in
`Dctf`, with the Tor interval of blueprint `sk-thm-sf-hom-ctf`. As in the blueprint, this goes
through Verdier biduality: `RHom(K, M) ≅ 𝔻(𝔻M ⊗ᴸ K)`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`).

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes. The blueprint states these results over
`k = 𝔽̄_q`; the algebraic closedness of `k` is used by Verdier biduality.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]

section DualizingHom

variable [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]

include a in
/-- Blueprint `proposition-six-operations-dctf--15`: Internal Hom for arbitrary finite-stage
constructible complexes.

For `X` separated of finite type over a field `k` with `dim X ≤ d`, a finite coefficient ring `Λ`
whose exponent is invertible on `k`, and `K, L ∈ Dctf(X, Λ)` with Tor intervals `[p, q]` and
`[r, s]`, the internal hom `RHom(K, L)` is bounded constructible with Tor amplitude in
`[r - q - 2d, s - p + 2d]`. As in the blueprint, `RHom(K, L) ≅ 𝔻_X(𝔻_X L ⊗ᴸ K)` by biduality
(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`), and `𝔻_X` carries the Tor
interval `[r, s]` into `[-s - 2d, -r]` (`AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual`). -/
theorem constructibleFiniteTor_derivedHom_of_isSeparated (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {p q r s : ℤ}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X p q K)
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) X L)
    (hLt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X r s L) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj L) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (r - q - 2 * (d : ℤ))
        (s - p + 2 * (d : ℤ)) ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj L) := by
  have hL' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L := ⟨hL, r, s, hLt⟩
  obtain ⟨e⟩ := nonempty_iso_verdierDual_verdierDual Λ a hL'
  obtain ⟨e'⟩ := nonempty_iso_derivedHom_verdierDual _ a K L e
  -- `𝔻_X L` has Tor amplitude in `[-s - 2d, -r]`, so `𝔻_X L ⊗ᴸ K` in `[p - s - 2d, q - r]`
  have hD := constructibleFiniteTor_verdierDual Λ a hL'
  have hDt := torAmplitudeIn_verdierDual Λ a d hd r s hL hLt
  have hT := constructibleFiniteTor_tensor Λ X hD ⟨hK, p, q, hKt⟩
  have hTt := torAmplitudeIn_tensor _ X _ _ _ _ hDt hKt
  have hDT := torAmplitudeIn_verdierDual Λ a d hd _ _ hT.1 hTt
  refine ⟨(boundedConstructible _ X).prop_of_iso e'.symm
    (constructibleFiniteTor_verdierDual Λ a hT).1, (torAmplitudeIn _ X _ _).prop_of_iso e'.symm ?_⟩
  exact hDT.mono (by omega) (by omega)

end DualizingHom

section DerivedHom

variable {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasInvertibleExponent Λ X] (m : ℕ) (hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
  (a b c d : ℤ)
  {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

For `X` of finite type over `k`, a finite `Λ` whose exponent is invertible on `X` and bounded
constructible `K` and `M` on `X_ét` of finite Tor amplitude, the internal hom `RHom(K, M)` is
bounded constructible. -/
theorem boundedConstructible_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  by_cases hX : IsEmpty X
  · exact boundedConstructible_of_openCover Λ (n := 0) Fin.elim0
      (fun x ↦ (hX.false x).elim) _ (fun i ↦ i.elim0)
  rw [not_isEmpty_iff] at hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  -- a finite cover by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : Fin t.card → X.Opens := fun i ↦ (t.equivFin.symm i).1.1
  refine boundedConstructible_of_openCover Λ U (fun x ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  have : IsAffine (U i) := (t.equivFin.symm i).1.2
  let aU := (U i).ι ≫ aX
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom _ (U i).ι K M
  exact (boundedConstructible _ _).prop_of_iso e.symm
    (constructibleFiniteTor_derivedHom_of_verdierDual _ aU
      (constructibleFiniteTor_verdierDual Λ aU) (nonempty_iso_verdierDual_verdierDual Λ aU)
      (constructibleFiniteTor_tensor Λ _)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hK, a, b, hKt⟩)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hM, c, d, hMt⟩)).1

include aX hm in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If `K` and `M` have Tor amplitude in `[a, b]` and `[c, d]` and `dim X ≤ m`, then `RHom(K, M)`
has Tor amplitude in `[c - b - 2m, d - a + 2m]`. The blueprint derives this from
`RHom(K, M) ≅ 𝔻_X (K ⊗ᴸ 𝔻_X M)`, the dualizing complex having cohomology in `[-2m, 0]`. The
statement is local on `X`, and on the separated affine opens it is
`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_isSeparated`
(`proposition-six-operations-dctf--15`). -/
theorem torAmplitudeIn_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  by_cases hX : IsEmpty X
  · exact torAmplitudeIn_of_openCover _ (n := 0) Fin.elim0
      (fun x ↦ (hX.false x).elim) _ (fun i ↦ i.elim0)
  rw [not_isEmpty_iff] at hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  -- a finite cover by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : Fin t.card → X.Opens := fun i ↦ (t.equivFin.symm i).1.1
  refine torAmplitudeIn_of_openCover _ U (fun x ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  have : IsAffine (U i) := (t.equivFin.symm i).1.2
  let aU := (U i).ι ≫ aX
  have hmU : topologicalKrullDim (U i) ≤ (m : WithBot ℕ∞) :=
    ((U i).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hm
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom _ (U i).ι K M
  have hKt' : torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) a b
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj K) :=
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ (U i).ι).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ (U i).ι a b hKt)
  have hMt' : torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) c d
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj M) :=
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) c d).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ (U i).ι).app M)
      (torAmplitudeIn_leftDerivedUpperStar _ (U i).ι c d hMt)
  exact (torAmplitudeIn _ _ _ _).prop_of_iso e.symm
    (constructibleFiniteTor_derivedHom_of_isSeparated (Λ := Λ) (a := aU) m hmU
      (hK.mapDerivedCategory_upperStar (U i).ι) hKt'
      (hM.mapDerivedCategory_upperStar (U i).ι) hMt').2

-- `aX` and the coefficient hypotheses are part of the blueprint setting, unused by the proof
set_option linter.unusedSectionVars false in
include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If moreover `K` is dualizable, the sharper interval `[c - b, d - a]` holds, from the local
identification `RHom(K, M) ≅ K^∨ ⊗ᴸ M`. It genuinely fails in general: for the origin
`i : {0} ⟶ 𝔸¹` both `i_* Λ` and `Λ` have Tor amplitude `[0, 0]` while
`RHom(i_* Λ, Λ) = i_* Λ(-1)[-2]`. -/
theorem torAmplitudeIn_derivedHom_of_isDualizable
    (_hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (_hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) :=
  torAmplitudeIn_derivedHom_of_isDualizable_aux _ hKt hKd hMt

include aX in
/-- Blueprint `proposition-six-operations-dctf--15`: Constructible internal Hom with a site-perfect
first variable.

If `K ∈ Dctf(X, Λ)` is site-perfect, that is dualizable, and `M` is bounded constructible, then
`RHom(K, M)` is bounded constructible; in particular every cohomology sheaf of `RHom(K, M)` is
constructible. Indeed `RHom(K, M) ≅ K^∨ ⊗ᴸ M`, where the coefficient dual `K^∨ = RHom(K, Λ)` is
bounded constructible (`AlgebraicGeometry.Etale.boundedConstructible_derivedHom`) of Tor
amplitude `[-b, -a]`, and the tensor product of two bounded constructible complexes, one of
them of finite Tor amplitude, is bounded constructible. -/
theorem boundedConstructible_derivedHom_of_isDualizable
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  -- the unit `Λ_X` is bounded constructible of Tor amplitude `[0, 0]`
  have hU : boundedConstructible (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
    (boundedConstructible _ X).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0)
  have hUt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0 (𝟙_ _) :=
    (torAmplitudeIn _ X 0 0).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))
  have hD : boundedConstructible (ModuleCat.{u + 1} Λ) X ((coefficientDual _ X).obj (op K)) :=
    boundedConstructible_derivedHom Λ aX a b 0 0 hK hKt hU hUt
  obtain ⟨_⟩ := hKd
  obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
  have hDt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b) (-a)
      ((coefficientDual _ X).obj (op K)) :=
    (torAmplitudeIn _ X _ _).prop_of_iso (coefficientDualIsoOfExactPairing Kᘁ K).symm
      (_root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt)
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor (isDualizable_of_hasRightDual K) M
  -- `K^∨ ⊗ᴸ M` is bounded, `K^∨` having finite Tor amplitude, with constructible homology
  obtain ⟨c', d', hcd⟩ :=
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).2 hM.1
  have : IsNoetherianRing Λ := inferInstance
  have hb : _root_.DerivedCategory.TStructure.t.bounded
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((coefficientDual _ X).obj (op K))).obj M) :=
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
      ⟨_, _,
        _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left hDt hcd⟩
  have hc := constructibleHomology_derivedTensor _ (fun F G hF hG n ↦ by
      have := (Etale.constructibleSheaf_iff _ _ _).mp hF
      have := (Etale.constructibleSheaf_iff _ _ _).mp hG
      exact (Etale.constructibleSheaf_iff _ _ _).mpr
        (isConstructibleSheaf_homology_tensor_singleFunctor Λ F G n)) hD hM
  exact (boundedConstructible _ X).prop_of_iso e ⟨hb, hc⟩

omit [Finite Λ] [HasInvertibleExponent Λ X] in
/-- If `K` is dualizable of Tor amplitude in `[a, b]`, then `RHom(K, G[0]) ≅ K^∨ ⊗ᴸ G[0]` is
concentrated in `[-b, -a]` for every sheaf `G`, the dual `K^∨` having Tor amplitude in
`[-b, -a]`. -/
theorem homologyConcentratedIn_derivedHom_singleFunctor_of_isDualizable
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    _root_.DerivedCategory.homologyConcentratedIn (-b) (-a)
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
  have h : _root_.DerivedCategory.homologyConcentratedIn (-b) (-a)
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((coefficientDual _ X).obj (op K))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
    obtain ⟨_⟩ := hKd
    obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
    have := _root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt
    exact (torAmplitudeIn _ X _ _).prop_of_iso
      (coefficientDualIsoOfExactPairing Kᘁ K).symm this G
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor hKd
    ((_root_.DerivedCategory.singleFunctor _ 0).obj G)
  exact homologyConcentratedIn_of_iso _ e h

include aX in
/-- Blueprint `proposition-six-operations-dctf--15`: Constructible internal Hom with a site-perfect
first variable.

For a finite locally free sheaf `F`, that is a constructible flat sheaf which is dualizable in
`D(X_ét, Λ)`, and a constructible sheaf `G`, the sheaves `𝓔xtʳ(F, G) = Hʳ RHom(F, G)` vanish
for `r ≠ 0`, and `𝓗om(F, G) = H⁰ RHom(F, G)` is constructible: `RHom(F, G)` is bounded
constructible and concentrated in degree `0`. Indeed `RHom(F, G) ≅ F^∨ ⊗ᴸ G` with `F^∨` of Tor
amplitude `[0, 0]`. -/
theorem boundedConstructible_derivedHom_singleFunctor_of_isDualizable
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] (hF : ObjectProperty.flat F)
    (hFd : IsDualizable ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ∧
      _root_.DerivedCategory.homologyConcentratedIn 0 0
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
  have hFt := _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hF
  refine ⟨boundedConstructible_derivedHom_of_isDualizable Λ aX 0 0
    (boundedConstructible_singleFunctor_obj F 0) hFt hFd
    (boundedConstructible_singleFunctor_obj G 0), ?_⟩
  exact homologyConcentratedIn_derivedHom_singleFunctor_of_isDualizable Λ 0 0 hFt hFd G

end DerivedHom

end Torsion

end Etale

end AlgebraicGeometry
