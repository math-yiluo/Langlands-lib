/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# Constructible preservation before biduality

Let `k` be a perfect field, `Λ` a finite ring whose exponent is invertible on `k`, and `X` a
separated scheme of finite type over `k` with `dim X ≤ d`. The Verdier dual
`𝔻_X = RHom(-, ω_X)`, `ω_X = Ra_X^! Λ`, carries `Dctf(X, Λ)` into itself, sending the Tor
interval `[a, b]` into `[-b - 2d, -a]` (blueprint
`lemma-verdier-duality-preserves-constructibility--1`).

The proof follows the blueprint. By Noetherian induction on the support, `K` is built by
open–closed triangles from objects `Rs_! P`, where `s : S ⟶ X` is a locally closed immersion of
an irreducible smooth stratum on which `P = s^* K` is site-perfect
(`AlgebraicGeometry.Etale.exists_dense_open_exactPairing`). On such a stratum

`𝔻_X (Rs_! P) ≅ Rs_* 𝔻_S P`

(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek`, blueprint
`lemma-internal-adjunction-two-exchange-formulas--1`), and smooth duality
(`proposition-exceptional-inverse-image-smooth-morphism`) gives `ω_S ≅ L[2r]` for a lisse invertible
`L`, so that `𝔻_S P ≅ P^∨ ⊗ᴸ L[2r]` has Tor amplitude `[-b - 2r, -a - 2r]`; the direct image theorem
(`proposition-six-operations-dctf--2`) makes `Rs_* 𝔻_S P` bounded constructible of Tor amplitude
`[-b - 2r, -a]`. The exactness of `RHom` in its first variable
(`definition-verdier-dual-evaluation--3`) assembles the pieces.

## Implementation notes

The blueprint works over `k = 𝔽̄_q`; its proof uses a stratification by *smooth* strata, which
exists over a perfect field (`AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField`).
The statements below therefore assume `k` perfect.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section TorAmplitude

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Tor amplitude in a fixed interval `[a, b]` is closed under extensions: tensoring a
distinguished triangle with a sheaf gives a distinguished triangle. -/
instance torAmplitudeIn_isTriangulatedClosed₂ (X : Scheme.{u}) (a b : ℤ) :
    (torAmplitudeIn A X a b).IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    refine ObjectProperty.le_isoClosure _ _ fun F ↦ ?_
    let G := (-⊗ᴸ-(X)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    obtain ⟨g₁, l₁⟩ := h₁ F
    obtain ⟨g₃, l₃⟩ := h₃ F
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
      _root_.DerivedCategory.TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

/-- The internal hom out of a zero object is zero. -/
lemma isZero_derivedHom_obj_of_isZero {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsZero K)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsZero (((RHom(X)[A]).obj (op K)).obj M) :=
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A)
  MonoidalCategory.isZero_ihom_obj_of_isZero hK M

end TorAmplitude

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `lemma-verdier-duality-preserves-constructibility--1`, the stratum step: let
`s : S ⟶ X` be a morphism of finite-type `k`-schemes with `S` smooth of pure relative dimension `r`
over `k` and `dim S ≤ r`, and let `P ∈ Dctf(S, Λ)` have Tor amplitude in `[a, b]` and a left dual in
`Dctf(S, Λ)` (`P` is site-perfect). Then `𝔻_X (Rs_! P) ≅ Rs_* 𝔻_S P`
(`lemma-internal-adjunction-two-exchange-formulas--1`) is bounded constructible of Tor amplitude in
`[-b - 2r, -a]`: by smooth duality (`proposition-exceptional-inverse-image-smooth-morphism`)
`ω_S ≅ L[2r]` with `L` lisse invertible, so that `𝔻_S P ≅ P^∨ ⊗ᴸ L[2r]` has Tor amplitude in
`[-b - 2r, -a - 2r]`, and `Rs_*` widens the upper end by `2r`
(`proposition-six-operations-dctf--2`). -/
theorem constructibleTorAmplitudeIn_verdierDual_rightDerivedLowerShriek_of_smooth
    {X S : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX] (s : S ⟶ X) [IsSeparated s] [HasCompactification s]
    [LocallyOfFiniteType (s ≫ aX)] [QuasiCompact (s ≫ aX)] [HasCompactification (s ≫ aX)]
    (r : ℕ) [SmoothOfRelativeDimension r (s ≫ aX)]
    (hr : topologicalKrullDim S ≤ (r : WithBot ℕ∞)) (a b : ℤ)
    {P D : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hPt : torAmplitudeIn (ModuleCat.{u + 1} Λ) S a b P)
    (hD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) S D) [ExactPairing D P] :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((verdierDual Λ aX).obj
          (op ((R(s)_![ModuleCat.{u + 1} Λ]).obj P))) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * r) (-a)
        ((verdierDual Λ aX).obj
          (op ((R(s)_![ModuleCat.{u + 1} Λ]).obj P))) := by
  have : IsNoetherianRing Λ := inferInstance
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : HasInvertibleExponent Λ S := .of_hom (s ≫ aX)
  obtain ⟨e₁⟩ := nonempty_iso_verdierDual_rightDerivedLowerShriek Λ s aX P
  -- smooth duality: `ω_S ≅ L[2r]`
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ (s ≫ aX) r
  obtain ⟨hLc, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  -- the dual `D` of `P` has Tor amplitude in `[-b, -a]`
  obtain ⟨_⟩ := nonempty_exactPairing_swap D P
  have hDt : torAmplitudeIn (ModuleCat.{u + 1} Λ) S (-b) (-a) D :=
    _root_.DerivedCategory.torAmplitudeIn_of_exactPairing hPt
  have hL₀ := torAmplitudeIn_singleFunctor_zero_of_flat _ L hLf
  have hMbc := boundedConstructible_tensor Λ S hD.1
    (DerivedCategory.boundedConstructible_singleFunctor_obj L 0) ⟨0, 0, hL₀⟩
  -- `𝔻_S P ≅ D ⊗ᴸ ω_S`
  have hS := constructibleTorAmplitudeIn_of_iso_tensor_shift _
    (derivedHomIsoDerivedTensorOfExactPairing _ D P (dualizingComplex _ (s ≫ aX))) eω hDt hL₀
    ((boundedConstructible _ S).le_shift _ _ hMbc)
  obtain ⟨⟨hSbc, -⟩, hSt⟩ := hS
  -- the direct image along `s`
  obtain ⟨N, hN0, hNΛ, hNX⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ
    ((verdierDual Λ (s ≫ aX)).obj (op P))
  have h₁ := constructibleFiniteTor_rightDerivedLowerStar Λ (s ≫ aX) aX s rfl
    ⟨hSbc, _, _, hSt⟩
  have h₂ := torAmplitudeIn_rightDerivedLowerStar _ (s ≫ aX) aX s rfl r hr _ _ N hN hNX hSbc hSt
  refine ⟨(constructibleFiniteTor _ X).prop_of_iso e₁.symm h₁,
    (torAmplitudeIn _ X _ _).prop_of_iso e₁.symm ?_⟩
  exact h₂.mono (by omega) (by omega)

omit [Finite Λ] in
/-- A zero object has Tor amplitude in every interval. -/
lemma torAmplitudeIn_of_isZero {X : Scheme.{u}} (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsZero K) : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K := fun F ↦ by
  have h : IsZero (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
    Functor.map_isZero ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) hK
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_isZero h a,
    _root_.DerivedCategory.TStructure.t.isLE_of_isZero h b⟩

variable [PerfectField k]

/-- Blueprint `lemma-verdier-duality-preserves-constructibility--1`, the dévissage: for `X`
separated of finite type over a perfect field `k` with `dim X ≤ d`, a reduced closed subscheme
`ι : Z ⟶ X` and `Q ∈ D^b_c(Z, Λ)` of Tor amplitude in `[a, b]`, the Verdier dual
`𝔻_X (Rι_! Q)` lies in `Dctf(X, Λ)` with Tor amplitude in `[-b - 2d, -a]`. By Noetherian
induction on the support: on an irreducible smooth open `W ⊆ Z` on which `Q` is site-perfect
this is the stratum step
`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_verdierDual_rightDerivedLowerShriek_of_smooth`,
and the open–closed triangle `j_! j^* Q ⟶ Q ⟶ i_* i^* Q` is carried by the exact functor
`Rι_!` and by `RHom(-, ω_X)` (`definition-verdier-dual-evaluation--3`) to a triangle whose outer
terms are handled by the stratum step and by induction. -/
theorem verdierDual_rightDerivedLowerShriek_of_isClosedImmersion {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    ∀ (T : TopologicalSpace.Closeds X) {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
      [IsReduced Z], Set.range ι.base = T → ∀ (a b : ℤ)
      {Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      boundedConstructible (ModuleCat.{u + 1} Λ) Z Q →
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b Q →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R(ι)_![ModuleCat.{u + 1} Λ]).obj Q))).obj
            (dualizingComplex _ aX)) ∧
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * d) (-a)
          (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R(ι)_![ModuleCat.{u + 1} Λ]).obj Q))).obj
            (dualizingComplex _ aX)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  have : HasInvertibleExponent Λ X := .of_hom aX
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro Z ι _ _ hT a b Q hQ hQt
  let aZ := ι ≫ aX
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  have : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian aZ }
  have : HasInvertibleExponent Λ Z := .of_hom aZ
  by_cases hZ : IsEmpty Z
  · have h0 := isZero_derivedHom_obj_of_isZero _
      ((R(ι)_![ModuleCat.{u + 1} Λ]).map_isZero (isZero_derivedCategory_of_isEmpty _ Z Q))
      (dualizingComplex _ aX)
    exact ⟨(constructibleFiniteTor _ X).prop_of_isZero h0, torAmplitudeIn_of_isZero Λ _ _ h0⟩
  rw [not_isEmpty_iff] at hZ
  -- a nonempty irreducible smooth open `W` on which `Q` is site-perfect
  obtain ⟨V, hVd, hV⟩ := exists_dense_open_exactPairing Λ ⟨hQ, a, b, hQt⟩
  have hsm : Dense (aZ.smoothLocus : Set Z) := aZ.dense_smoothLocus_of_perfectField
  have hOd : Dense ((V ⊓ aZ.smoothLocus : Z.Opens) : Set Z) :=
    hVd.inter_of_isOpen_left hsm V.isOpen
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    {hZ.some} isIrreducible_singleton
  obtain ⟨o, ho, hon, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  let W : Z.Opens := ⟨o, ho⟩ ⊓ (V ⊓ aZ.smoothLocus)
  have hWne : (W : Set Z).Nonempty := dense_iff_inter_open.1 hOd o ho hon
  have hWirr : IsIrreducible (W : Set Z) :=
    ⟨hWne, hC.1.isPreirreducible.open_subset
      W.isOpen (Set.inter_subset_left.trans hoC)⟩
  have : IrreducibleSpace W := Subtype.irreducibleSpace hWirr
  have hWV : W ≤ V := inf_le_right.trans inf_le_left
  have : Smooth (W.ι ≫ aZ) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      eq_top_iff]
    intro x _
    exact (inf_le_right.trans inf_le_right : W ≤ aZ.smoothLocus) x.2
  have hdW : topologicalKrullDim W ≤ (d : WithBot ℕ∞) :=
    ((W.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans
      ι.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hd
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim W = n := by
    have : Nonempty W := hWne.to_subtype
    have : Nonempty (TopologicalSpace.IrreducibleCloseds W) :=
      ⟨⟨closure {Classical.arbitrary W}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1
      (Order.krullDim_eq_bot_iff.not.2
        (not_isEmpty_of_nonempty (TopologicalSpace.IrreducibleCloseds W)))
    induction m with
    | top =>
      have hdW' : Order.krullDim (TopologicalSpace.IrreducibleCloseds W) ≤ d := hdW
      rw [← hm] at hdW'
      exact absurd (WithBot.coe_le_coe.mp hdW') (by simp)
    | coe n => exact ⟨n, hm.symm⟩
  have hnd : n ≤ d := by
    rw [hn] at hdW
    exact_mod_cast hdW
  have : SmoothOfRelativeDimension n (W.ι ≫ aZ) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq (W.ι ≫ aZ) n).2 hn
  have hn' : topologicalKrullDim W ≤ (n : WithBot ℕ∞) := hn.le
  -- the open–closed triangle on `Z`, carried to `X` by `Rι_!`
  let i := W.closedComplement
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification W.ι := (Compactification.ofIsOpenImmersion W.ι).hasCompactification
  have : HasCompactification (W.ι ≫ ι) :=
    Compactification.hasCompactification
      (⟨Z, ι, W.ι, rfl, inferInstance, inferInstance⟩ : Compactification (W.ι ≫ ι))
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) W.ι i (by simp [i]) Q
  have hw' := (R(ι)_![ModuleCat.{u + 1} Λ]).map_distinguished _ hw
  -- the open part: the stratum step for `s = W.ι ≫ ι`
  have key₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R(ι)_![ModuleCat.{u + 1} Λ]).obj
          (D((W.ι)_!open[ModuleCat.{u + 1} Λ]).obj (D((W.ι)^*[ModuleCat.{u + 1} Λ]).obj Q))))).obj
            (dualizingComplex _ aX)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * d) (-a)
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R(ι)_![ModuleCat.{u + 1} Λ]).obj
          (D((W.ι)_!open[ModuleCat.{u + 1} Λ]).obj (D((W.ι)^*[ModuleCat.{u + 1} Λ]).obj Q))))).obj
            (dualizingComplex _ aX)) := by
    obtain ⟨D, hD, ⟨_⟩⟩ := hV W hWV
    have : SmoothOfRelativeDimension n ((W.ι ≫ ι) ≫ aX) := by
      rw [Category.assoc]; infer_instance
    obtain ⟨ec⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ W.ι ι
    let P := (L((W.ι)^*[ModuleCat.{u + 1} Λ])).obj Q
    let e : (R(ι)_![ModuleCat.{u + 1} Λ]).obj
        (D((W.ι)_!open[ModuleCat.{u + 1} Λ]).obj (D((W.ι)^*[ModuleCat.{u + 1} Λ]).obj Q)) ≅
          (R(W.ι ≫ ι)_![ModuleCat.{u + 1} Λ]).obj P :=
      (R(ι)_![ModuleCat.{u + 1} Λ]).mapIso
        (D((W.ι)_!open[ModuleCat.{u + 1} Λ]).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory _ W.ι).app Q).symm ≪≫
        ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ W.ι).app P).symm) ≪≫ (ec.app P).symm
    have hPt : torAmplitudeIn (ModuleCat.{u + 1} Λ) W a b P :=
      torAmplitudeIn_leftDerivedUpperStar _ W.ι a b hQt
    obtain ⟨h₁, h₂⟩ := constructibleTorAmplitudeIn_verdierDual_rightDerivedLowerShriek_of_smooth
      Λ aX (W.ι ≫ ι) n hn' a b hPt hD
    let e' := ((RHom(X)[ModuleCat.{u + 1} Λ]).mapIso e.op).app (dualizingComplex _ aX)
    exact ⟨(constructibleFiniteTor _ X).prop_of_iso e' h₁,
      (torAmplitudeIn _ X _ _).prop_of_iso e' (h₂.mono (by omega) le_rfl)⟩
  -- the closed part, by induction
  have key₃ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R(ι)_![ModuleCat.{u + 1} Λ]).obj
          ((R((i)_*[ModuleCat.{u + 1} Λ])).obj (D((i)^*[ModuleCat.{u + 1} Λ]).obj Q))))).obj
            (dualizingComplex _ aX)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * d) (-a)
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R(ι)_![ModuleCat.{u + 1} Λ]).obj
          ((R((i)_*[ModuleCat.{u + 1} Λ])).obj (D((i)^*[ModuleCat.{u + 1} Λ]).obj Q))))).obj
            (dualizingComplex _ aX)) := by
    have hlt : (⟨Set.range (i ≫ ι).base, (i ≫ ι).isClosedEmbedding.isClosed_range⟩ :
        TopologicalSpace.Closeds X) < T := by
      rw [← SetLike.coe_ssubset_coe, TopologicalSpace.Closeds.coe_mk, ← hT, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.range_comp]
      refine (Set.image_subset_range _ _).ssubset_of_ne fun h ↦ ?_
      obtain ⟨z, hz⟩ := hWne
      obtain ⟨y, hy, hyz⟩ : ι.base z ∈ ι.base '' Set.range i.base := h ▸ ⟨z, rfl⟩
      rw [ι.isClosedEmbedding.injective hyz, W.range_closedComplement] at hy
      exact hy hz
    obtain ⟨ec⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ i ι
    let e : (R(ι)_![ModuleCat.{u + 1} Λ]).obj
        ((R((i)_*[ModuleCat.{u + 1} Λ])).obj (D((i)^*[ModuleCat.{u + 1} Λ]).obj Q)) ≅
          (R(i ≫ ι)_![ModuleCat.{u + 1} Λ]).obj (D((i)^*[ModuleCat.{u + 1} Λ]).obj Q) :=
      (R(ι)_![ModuleCat.{u + 1} Λ]).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).app _).symm ≪≫ (ec.app _).symm
    have hQt' : torAmplitudeIn (ModuleCat.{u + 1} Λ) _ a b (D((i)^*[ModuleCat.{u + 1} Λ]).obj Q) :=
      (torAmplitudeIn _ _ a b).prop_of_iso ((leftDerivedUpperStarIsoMapDerivedCategory _ i).app Q)
        (torAmplitudeIn_leftDerivedUpperStar _ i a b hQt)
    obtain ⟨h₁, h₂⟩ := ih _ hlt (i ≫ ι) rfl a b (hQ.mapDerivedCategory_upperStar i) hQt'
    let e' := ((RHom(X)[ModuleCat.{u + 1} Λ]).mapIso e.op).app (dualizingComplex _ aX)
    exact ⟨(constructibleFiniteTor _ X).prop_of_iso e' h₁,
      (torAmplitudeIn _ X _ _).prop_of_iso e' h₂⟩
  have hP₁ := derivedHom_mem_of_distTriang_left
    (constructibleFiniteTor (ModuleCat.{u + 1} Λ) X) (dualizingComplex _ aX) _ hw'
  have hP₂ := derivedHom_mem_of_distTriang_left
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * d) (-a)) (dualizingComplex _ aX) _ hw'
  exact ⟨hP₁ key₁.1 key₃.1, hP₂ key₁.2 key₃.2⟩

/-- Blueprint `lemma-verdier-duality-preserves-constructibility--1`: Constructible preservation
before biduality.

Let `X` be separated of finite type over a perfect field `k`, `Λ` a finite ring whose exponent
is invertible on `k`, `ω_X = Ra_X^! Λ` and `𝔻_X = RHom(-, ω_X)`. If `dim X ≤ d` and `K` is
bounded constructible of Tor amplitude in `[a, b]`, then `𝔻_X K` lies in `Dctf(X, Λ)` with Tor
amplitude in `[-b - 2d, -a]`. This is
`AlgebraicGeometry.Etale.verdierDual_rightDerivedLowerShriek_of_isClosedImmersion` for the
reduced closed subscheme `r : X_red ⟶ X`, through which `K ≅ Rr_* r^* K` factors. -/
theorem constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((verdierDual Λ aX).obj (op K)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * d) (-a)
        ((verdierDual Λ aX).obj (op K)) := by
  -- `K ≅ Rr_* r^* K` for the reduced closed subscheme `r : X_red ⟶ X`
  let r := (⊥ : X.Opens).closedComplement
  have : IsEmpty ((⊥ : X.Opens) : Scheme.{u}) := ⟨fun ⟨_, hx⟩ ↦ hx⟩
  have hr₀ : Set.range r.base = Set.univ := by
    simpa using (⊥ : X.Opens).range_closedComplement
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) (⊥ : X.Opens).ι r
    (by simpa using hr₀) K
  have hr : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).unit.app K) :=
    (Triangle.isZero₁_iff_isIso₂ _ hw).1 (Functor.map_isZero _
      (isZero_derivedCategory_of_isEmpty _ (⊥ : X.Opens) _))
  let Q := D((r)^*[ModuleCat.{u + 1} Λ]).obj K
  let e : K ≅ (R(r)_![ModuleCat.{u + 1} Λ]).obj Q :=
    asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).unit.app K) ≪≫
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ r).app Q).symm
  have hQt : torAmplitudeIn (ModuleCat.{u + 1} Λ) _ a b Q :=
    (torAmplitudeIn _ _ a b).prop_of_iso ((leftDerivedUpperStarIsoMapDerivedCategory _ r).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ r a b hKt)
  obtain ⟨h₁, h₂⟩ := verdierDual_rightDerivedLowerShriek_of_isClosedImmersion Λ aX d hd ⊤ r
    (by simpa using hr₀) a b (hK.mapDerivedCategory_upperStar r) hQt
  let e' := ((RHom(X)[ModuleCat.{u + 1} Λ]).mapIso e.op).app (dualizingComplex _ aX)
  exact ⟨(constructibleFiniteTor _ X).prop_of_iso e' h₁, (torAmplitudeIn _ X _ _).prop_of_iso e' h₂⟩

end Etale

end AlgebraicGeometry
