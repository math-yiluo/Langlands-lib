/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualLocal
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation

/-!
# The Tor bound of the Verdier dual, by noetherian induction

Let `X` be separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and
`Λ` a finite ring whose exponent is invertible in `k`. If `K ∈ Dᵇc(X, Λ)` has Tor amplitude in
`[a, b]`, then `𝔻_X K = RHom(K, ω_X)` is bounded constructible with Tor amplitude in
`[-b - 2d, -a]`
(`AlgebraicGeometry.Etale.boundedConstructible_and_torAmplitudeIn_verdierDual_of_isAlgClosed`,
`lemma-verdier-duality-preserves-constructibility--1`).

The proof is a noetherian induction on the support, along the localization triangles of the
*dualizing complex* `Ri_! Ri^! ω ⟶ ω ⟶ Rj_* j^* ω ⟶` for a closed immersion `i` with open
complement `j`, to which the triangulated functor `RHom(K, -)` is applied:

- `RHom(K, Ri_! Ri^! ω_Y) ≅ Ri_! 𝔻_Z(i^* K)`, handled by induction;
- `RHom(K, Rj_* j^* ω_Y) ≅ Rj_* 𝔻_U(j^* K)`; on a dense open `U` of the reduction of the support
  which is smooth of pure relative dimension `n ≤ d`, irreducible, and on which a flat model of
  `K` is lisse, `𝔻_U(j^* K)` is bounded constructible with Tor amplitude `[-b - 2n, -a - 2n]`
  (`AlgebraicGeometry.Etale.exists_boundedConstructible_and_torAmplitudeIn_verdierDual`), and the
  direct image `Rj_*` moves this to `[-b - 2n, -a]`
  (`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`,
  `proposition-six-operations-dctf--2`).

Working with the localization triangles of `ω` rather than of `K` only uses the exactness of
the internal hom in its *second* variable.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-! ### Generalities -/

variable {Λ} in
/-- The Verdier dual only depends on the structure morphism. -/
lemma verdierDual_obj_congr {X S : Scheme.{u}} {g₁ g₂ : X ⟶ S} (h : g₁ = g₂)
    [HasCompactification g₁] [HasCompactification g₂] (K : DerivedCategoryModule Λ X) :
    (verdierDual Λ g₁).obj (op K) =
      (verdierDual Λ g₂).obj (op K) := by
  subst h
  rfl

variable {Λ} in
omit [Finite Λ] in
/-- A zero object is bounded constructible and has every Tor amplitude. -/
lemma boundedConstructible_and_torAmplitudeIn_of_isZero {X : Scheme.{u}}
    {N : DerivedCategoryModule Λ X} (hN : IsZero N) (a b : ℤ) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X N ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b N :=
  ⟨(boundedConstructible _ X).prop_of_isZero hN, torAmplitudeIn_of_isZero _ a b hN⟩

variable {Λ} in
omit [Finite Λ] in
/-- A complex of Tor amplitude in `[a, b]` with `b < a` is zero. -/
lemma isZero_of_torAmplitudeIn_of_lt {X : Scheme.{u}} {K : DerivedCategoryModule Λ X} {a b : ℤ}
    (h : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hab : b < a) : IsZero K := by
  obtain ⟨h₁, h₂⟩ := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn h
  have : K.IsGE a := h₁
  have : K.IsLE b := h₂
  exact _root_.DerivedCategory.TStructure.t.isZero K b a hab

/-! ### The two pieces of the localization triangle of the dualizing complex -/

/-- **The closed piece.** For a closed immersion `i : Z ⟶ Y` and `K` on `Y`,
`RHom(K, Ri_! Ri^! ω_Y) ≅ Ri_! 𝔻_Z(i^* K)`. -/
theorem nonempty_iso_derivedHom_rightDerivedLowerShriek_dualizingComplex
    {Z Y S : Scheme.{u}} (aY : Y ⟶ S) [HasCompactification aY] (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasCompactification i] [HasCompactification (i ≫ aY)] [QuasiCompact (i ≫ aY)]
    (K : DerivedCategoryModule Λ Y) :
    Nonempty (((RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj (dualizingComplex _ aY))) ≅
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((verdierDual Λ (i ≫ aY)).obj
        (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)))) := by
  obtain ⟨eω⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ i aY
  let eS := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i
  let N := (R(i)^![Λ]).obj (dualizingComplex _ aY)
  obtain ⟨eH⟩ := nonempty_iso_derivedHom_rightDerivedLowerStar Λ i K N
  exact ⟨((RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)).mapIso (eS.app N) ≪≫ eH ≪≫
    (eS.app _).symm ≪≫ (R(i)_![ModuleCat.{u + 1} Λ]).mapIso
      (((RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
        eω)⟩

/-- **The open piece.** For an open immersion `j : U ⟶ Y` and `K` on `Y`,
`RHom(K, Rj_* j^* ω_Y) ≅ Rj_* 𝔻_U(j^* K)`. -/
theorem nonempty_iso_derivedHom_rightDerivedLowerStar_dualizingComplex {U Y S : Scheme.{u}}
    (aY : Y ⟶ S) [HasCompactification aY] (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j] [HasCompactification (j ≫ aY)] [QuasiCompact (j ≫ aY)]
    (K : DerivedCategoryModule Λ Y) :
    Nonempty (((RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)).obj
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
          ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ aY))) ≅
      (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ (j ≫ aY)).obj
        (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)))) := by
  obtain ⟨eω⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ j aY
  obtain ⟨eH⟩ := nonempty_iso_derivedHom_rightDerivedLowerStar Λ j K
    ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ aY))
  exact ⟨eH ≪≫ (R((j)_*[ModuleCat.{u + 1} Λ])).mapIso
    (((RHom(U)[ModuleCat.{u + 1} Λ]).obj (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
        ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _).symm ≪≫ eω))⟩

/-! ### The localization step -/

/-- **The localization step.** Let `Y` be of finite type over a field `k`, `j : U ⟶ Y` a
quasi-compact open immersion with `dim U ≤ e` and `i : Z ⟶ Y` a closed immersion onto the
complement. If the Verdier duals `𝔻_Z(i^* K)` and `𝔻_U(j^* K)` are bounded constructible with Tor
amplitude in `[α, β]` and `[α, β - 2e]` respectively, then `𝔻_Y K` is bounded constructible with
Tor amplitude in `[α, β]`: apply the triangulated functor `RHom(K, -)` to the localization
triangle `Ri_! Ri^! ω ⟶ ω ⟶ Rj_* j^* ω ⟶`, and use that `Ri_!` preserves both properties
while `Rj_*` widens the Tor amplitude by `2 dim U`. -/
theorem boundedConstructible_and_torAmplitudeIn_verdierDual_of_localization {k : Type u}
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {Y U Z : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [HasCompactification j]
    [HasCompactification (j ≫ aY)] (i : Z ⟶ Y) [IsClosedImmersion i] [HasCompactification i]
    [HasCompactification (i ≫ aY)] (hij : Set.range i.base = (Set.range j.base)ᶜ) (e : ℕ)
    (he : topologicalKrullDim U ≤ (e : WithBot ℕ∞)) (K : DerivedCategoryModule Λ Y) {α β : ℤ}
    (hZ : boundedConstructible (ModuleCat.{u + 1} Λ) Z
        ((verdierDual Λ (i ≫ aY)).obj
          (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Z α β
        ((verdierDual Λ (i ≫ aY)).obj
          (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))))
    (hU : boundedConstructible (ModuleCat.{u + 1} Λ) U
        ((verdierDual Λ (j ≫ aY)).obj
          (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) U α (β - 2 * e)
        ((verdierDual Λ (j ≫ aY)).obj
          (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)))) :
    boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((verdierDual Λ aY).obj (op K)) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y α β
        ((verdierDual Λ aY).obj (op K)) := by
  have : IsNoetherianRing Λ := inferInstance
  have : HasInvertibleExponent Λ Y := .of_hom aY
  let F := (RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op K)
  have : F.IsTriangulated := (derivedTensorHomAdjunction _ K).isTriangulated_rightAdjoint
  have hT := F.map_distinguished _ (supportedLocalizationTriangle_mem_distTriang
    Λ i j hij (dualizingComplex _ aY))
  -- the closed piece
  obtain ⟨eZ⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek_dualizingComplex Λ aY i K
  let eS := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i
  have h₁ : boundedConstructible (ModuleCat.{u + 1} Λ) Y
      (F.obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj (dualizingComplex _ aY)))) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y α β
      (F.obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj (dualizingComplex _ aY)))) :=
    ⟨(boundedConstructible _ Y).prop_of_iso (eZ ≪≫ eS.app _).symm
      (boundedConstructible_rightDerivedLowerStar_of_finite Λ (i ≫ aY) aY i rfl hZ.1),
    (torAmplitudeIn _ Y α β).prop_of_iso eZ.symm
      (torAmplitudeIn_rightDerivedLowerShriek_of_isClosedImmersion (ModuleCat.{u + 1} Λ) i
        (fun L ↦ hasProjectionFormula_of_finite Λ i _ L) hZ.2)⟩
  -- the open piece
  obtain ⟨eU⟩ := nonempty_iso_derivedHom_rightDerivedLowerStar_dualizingComplex Λ aY j K
  obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
  have : NeZero N := ⟨hN0.ne'⟩
  have hUt := torAmplitudeIn_rightDerivedLowerStar Λ (j ≫ aY) aY j rfl e he
    α (β - 2 * e) N (nsmul_id_eq_zero_of_natCast_eq_zero hNΛ _) hNY hU.1 hU.2
  have h₃ : boundedConstructible (ModuleCat.{u + 1} Λ) Y
      (F.obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ aY)))) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y α β
      (F.obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ aY)))) :=
    ⟨(boundedConstructible _ Y).prop_of_iso eU.symm
      (boundedConstructible_rightDerivedLowerStar_of_finite Λ (j ≫ aY) aY j rfl hU.1),
    (torAmplitudeIn _ Y α β).prop_of_iso eU.symm (by simpa using hUt)⟩
  exact ⟨(boundedConstructible _ Y).ext_of_isTriangulatedClosed₂ _ hT h₁.1 h₃.1,
    torAmplitudeIn_obj₂_of_distTriang Λ _ hT h₁.2 h₃.2⟩

/-! ### A lisse smooth open -/

variable {Λ} in
omit [Finite Λ] in
/-- Finitely many constructible sheaves on a noetherian scheme are finite locally constant on a
common dense open: intersect the dense opens of generic constancy of the individual sheaves. -/
lemma exists_dense_open_forall_isFiniteLocallyConstantSheaf {X : Scheme.{u}} [IsNoetherian X]
    (n : ℕ) (F : Fin n → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ q, IsConstructibleSheaf (F q)) :
    ∃ W : X.Opens, Dense (W : Set X) ∧
      ∀ q, IsFiniteLocallyConstantSheaf ((W.ι)^*[ModuleCat.{u + 1} Λ].obj (F q)) := by
  induction n with
  | zero => exact ⟨⊤, by simp, fun q ↦ q.elim0⟩
  | succ n ih =>
    obtain ⟨W, hWd, hW⟩ := ih (fun q ↦ F q.castSucc) (fun q ↦ hF _)
    have := hF (Fin.last n)
    obtain ⟨V, hVd, hV⟩ := IsConstructibleSheaf.exists_dense_open (F (Fin.last n))
    refine ⟨W ⊓ V, hWd.inter_of_isOpen_left hVd W.isOpen, fun q ↦ ?_⟩
    refine Fin.lastCases ?_ (fun q ↦ ?_) q
    · exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (W ⊓ V).ι V.ι
        (by simp) _
    · have := hW q
      exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset (W ⊓ V).ι W.ι
        (by simp) _

variable {Λ} in
/-- A nonempty scheme of finite type over a field has a natural number as its dimension. -/
lemma exists_topologicalKrullDim_eq {k : Type u} [Field k] {X : Scheme.{u}} [Nonempty X]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : 0 ≤ topologicalKrullDim X := Order.krullDim_nonneg
  generalize topologicalKrullDim X = m at hd h0
  induction m using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hd fun h ↦ ENat.natCast_ne_top d (top_le_iff.1 (WithBot.coe_le_coe.1 h))
    | coe n => exact ⟨n, rfl⟩

/-- **A lisse smooth open.** Let `Z` be a nonempty reduced scheme of finite type over a perfect
field `k`, and `K` a bounded constructible complex on `Z` of Tor amplitude in `[a, b]`, `a ≤ b`.
There is a nonempty irreducible open `O ⊆ Z`, smooth of some relative dimension `n` over `k`, on
which `K` is represented by a bounded complex in degrees `[a, b]` of flat finite locally constant
sheaves. -/
theorem exists_opens_smooth_isFiniteLocallyConstantSheaf {k : Type u} [Field k] [PerfectField k]
    {Z : Scheme.{u}} [IsReduced Z] [Nonempty Z] (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ]
    [QuasiCompact aZ] {a b : ℤ} (hab : a ≤ b) {K : DerivedCategoryModule Λ Z}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) Z K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a b K) :
    ∃ (O : Z.Opens) (_ : Nonempty O) (_ : IrreducibleSpace O) (n : ℕ)
      (_ : SmoothOfRelativeDimension n (O.ι ≫ aZ))
      (P : CochainComplex (Sheaf O.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ),
      IsBoundedFlatComplex Λ a b P ∧ (∀ q, IsFiniteLocallyConstantSheaf (P.X q)) ∧
        Nonempty ((L((O.ι)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (_root_.DerivedCategory.Q).obj P) := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  have : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian aZ }
  -- a flat constructible model of `K`
  obtain ⟨P, hP, hPc, ⟨eP⟩⟩ := (hasTorAmplitudeIn_iff_exists_flatConstructibleModel Λ a b hab K
    hK).1 (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hKt)
  -- a dense open on which the terms of the model are lisse
  let m := (b + 1 - a).toNat
  obtain ⟨W, hWd, hW⟩ := exists_dense_open_forall_isFiniteLocallyConstantSheaf m
    (fun q ↦ P.X (a + (q : ℕ))) (fun q ↦ hPc _)
  -- intersect with the smooth locus
  let S := aZ.smoothLocus
  have hSd : Dense (S : Set Z) := aZ.dense_smoothLocus_of_perfectField
  have hWS : Dense ((W ⊓ S : Z.Opens) : Set Z) := hWd.inter_of_isOpen_left hSd W.isOpen
  -- an irreducible open inside `W ⊓ S`
  obtain ⟨w, hw⟩ := hWS.nonempty
  let C := irreducibleComponent w
  have hC : C ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents w
  obtain ⟨o, ho, hon, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨z, hzo, hzWS⟩ : (o ∩ (W ⊓ S : Z.Opens)).Nonempty := by
    obtain ⟨z, hzC, hzo, hzWS⟩ := isIrreducible_irreducibleComponent.2 o _ ho (W ⊓ S).isOpen
      (hon.mono fun x hx ↦ ⟨hoC hx, hx⟩) ⟨w, mem_irreducibleComponent, hw⟩
    exact ⟨z, hzo, hzWS⟩
  let O : Z.Opens := ⟨o ∩ (W ⊓ S : Z.Opens), ho.inter (W ⊓ S).isOpen⟩
  have hOW : O ≤ W := fun x hx ↦ hx.2.1
  have hOS : O ≤ S := fun x hx ↦ hx.2.2
  have : Nonempty O := ⟨⟨z, hzo, hzWS⟩⟩
  have : IrreducibleSpace O := Subtype.irreducibleSpace ⟨⟨z, hzo, hzWS⟩,
    isIrreducible_irreducibleComponent.2.open_subset O.isOpen fun x hx ↦ hoC hx.1⟩
  have : TopologicalSpace.NoetherianSpace O := O.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact O.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  -- `O` is smooth of some relative dimension
  have : Smooth (O.ι ≫ aZ) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    rintro x -
    exact hOS x.2
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq (O.ι ≫ aZ)
  have hsm := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq (O.ι ≫ aZ) n).2 hn
  -- the restricted model
  let P' := (((O.ι)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  refine ⟨O, inferInstance, inferInstance, n, hsm, P',
    ⟨fun q hq ↦ ((O.ι)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 q hq), fun q ↦
      Functor.PreservesFlat.flat_obj (F := (O.ι)^*[ModuleCat.{u + 1} Λ]) (hP.2 q)⟩,
    fun q ↦ ?_, ⟨(L((O.ι)^*[ModuleCat.{u + 1} Λ])).mapIso eP ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory _ O.ι).app _ ≪≫
      ((O.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app P⟩⟩
  by_cases hq : a ≤ q ∧ q ≤ b
  · have hi : a + ((⟨(q - a).toNat, by omega⟩ : Fin m) : ℕ) = q := by
      simp only
      omega
    have hWq := hW ⟨(q - a).toNat, by omega⟩
    rw [hi] at hWq
    exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset O.ι W.ι
      (by simpa using hOW) _
  · exact IsFiniteLocallyConstantSheaf.of_isZero
      (((O.ι)^*[ModuleCat.{u + 1} Λ]).map_isZero (hP.1 q (by omega)))

end Etale

end AlgebraicGeometry
