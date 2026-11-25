/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitSmoothSurface
public import WeilConjectures.AlgebraicGeometry.RegularDivisor
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
public import WeilConjectures.AlgebraicGeometry.StrictLocalizationFibre
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import WeilConjectures.ConstructibleSheaf.EllMonodromy
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionStrictlyLocal
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.TraceFormula.TransverseBoundary.Boundary
public import WeilConjectures.TraceFormula.TransverseBoundary.OfRegularDivisors
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology

/-!
# Restriction to a transverse punctured curve

Let `Z` be a smooth surface over an algebraically closed field `k` (or an étale limit of such),
`X, Y ⊆ Z` regular divisors meeting transversely at exactly one point `z`, `j : Z - Y ⟶ Z` and
`i : Z - (X ∪ Y) ⟶ Z - Y` the open immersions, and `E` a bounded complex of `Λ`-modules on
`Z - (X ∪ Y)` with finite `ℓ`-group monodromy, `Λ` a finite `ℓ`-primary ring. Put
`M = Rj_* i_! E`. The transverse boundary calculation (blueprint
`lemma-cohomology-near-two-transverse-divisors`, stated here as
`AlgebraicGeometry.Etale.transverseBoundary`) gives `M_z = 0` and, for `Y` connected, that the
restriction `RΓ(Y, M|_Y) ⟶ M_s` is zero at every closed point `s ≠ z` of `Y`.

From this we deduce (blueprint `lemma-restriction-punctured-curve`) that for a closed curve
`C ⊆ Z` with `C ∩ Y = {s}` the restriction map
```
RΓ(Z - Y, i_! E) ⟶ RΓ(C_(s) - s, (i_! E)|_{C_(s) - s})
```
to the punctured strict localization of `C` at `s` is zero. Following the blueprint
(`lemma-restriction-punctured-curve--1`), the restriction factors through the restriction
`RΓ(Y, M|_Y) ⟶ M_s` to the stalk at `s`; here the stalk `M_s` is computed on the strictly local
scheme `C_(s)` itself rather than on the strict localization of `Z`. In fact only this is used of
`C_(s) - s`: it maps to `Z - Y` through a strictly local scheme `S` over `Z` whose closed point
maps to `s` (`AlgebraicGeometry.Etale.globalSectionsRestriction_eq_zero_of_strictlyLocal`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime]
  {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  {Z : Over (Spec (.of k))} {X Y : Scheme.{u}} {iX : X ⟶ Z.left} {iY : Y ⟶ Z.left}
  {UY UXY : Z.left.Opens}

/-- The complex `M = Rj_* i_! E` on `Z` of the transverse boundary calculation (blueprint
`lemma-cohomology-near-two-transverse-divisors`), for `j : Z - Y ⟶ Z` and
`i : Z - (X ∪ Y) ⟶ Z - Y`. -/
noncomputable abbrev transverseBoundaryComplex (hXY : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ((UY.ι)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.obj
    (((Z.left.homOfLE hXY)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E)

/-- **Transverse boundary calculation** (blueprint `lemma-cohomology-near-two-transverse-divisors`).

Let `Z` be a regular, locally noetherian scheme over the algebraically closed field `k` of
characteristic `≠ ℓ` which is a smooth surface, or an étale limit with affine transition maps of
such surfaces, and `X, Y` regular divisors meeting transversely at exactly one point `z`: their
scheme-theoretic intersection is the reduced point `z` (`MeetTransverselyAt`) and has codimension
two in `Z` (`hXY`), i.e. local equations of `X` and `Y` form a regular system of parameters at
`z`. Let `Z - Y` (`UY`) and `Z - (X ∪ Y)` (`UXY`) be the open complements,
`j : Z - Y ⟶ Z` and `i : Z - (X ∪ Y) ⟶ Z - Y`. Let `Λ` be a finite `ℓ`-primary ring and `E` a
bounded complex of `Λ`-modules on `Z - (X ∪ Y)` with finite locally constant cohomology whose
monodromy factors through a finite `ℓ`-group. Put `M = Rj_* i_! E`. Then
1. `M_z = 0`: the pullback of `M` to every geometric point over `z` vanishes;
2. `M|_{Y - z}` has finite locally constant cohomology;
3. if `Y` is connected, then for every closed point `s ≠ z` of `Y` and every geometric point
   `s̄` over `s`, the restriction map `RΓ(Y, M|_Y) ⟶ M_s = RΓ(s̄, s̄^* M|_Y)` is zero.

This is `AlgebraicGeometry.Scheme.TransverseCorner.transverse_boundary` for the transverse corner
`AlgebraicGeometry.Scheme.TransverseCorner.ofRegularDivisors`, with the derived pullbacks `Lf^*`
replaced by the levelwise pullbacks `D(f^*)`.

The codimension two hypothesis `hXY` is needed: without it `Z` could be the spectrum of a
discrete valuation ring (an étale limit of smooth surfaces, the local ring of a surface at the
generic point of a curve) with `X = Y` its closed point, and then `M_z` contains `Λ` in degree
`0`. -/
theorem transverseBoundary (hℓ : (ℓ : k) ≠ 0) (hΛ : IsNilpotent (ℓ : Λ))
    (hZ : IsEtaleLimitOfSmoothSurfaces Z) [IsLocallyNoetherian Z.left] [IsRegular Z.left]
    (hX : IsRegularDivisor iX) (hY : IsRegularDivisor iY)
    (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX))
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) :
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (z' : Spec (.of Ω) ⟶ Z.left),
      Set.range z' = {z} →
        IsZero (((z')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          (transverseBoundaryComplex hle E))) ∧
    (∀ V : Y.Opens, (V : Set Y) = (iY ⁻¹' {z})ᶜ → ∀ n : ℤ,
      Scheme.IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
        (((V.ι ≫ iY)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          (transverseBoundaryComplex hle E)))) ∧
    (ConnectedSpace Y → ∀ (s : Y), IsClosed ({s} : Set Y) → iY s ≠ z →
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s' : Spec (.of Ω) ⟶ Y), Set.range s' = {s} →
        globalSectionsRestriction s' (((iY)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          (transverseBoundaryComplex hle E)) = 0) := by
  let C := Scheme.TransverseCorner.ofRegularDivisors hZ hX hY z hz hXY hUY hUXY hle
  obtain ⟨h₁, h₂, h₃⟩ := C.transverse_boundary hℓ Λ hΛ E hE
  refine ⟨fun Ω _ _ z' hz' ↦ ?_, fun V hV n ↦ ?_, fun hYc s _ hsz Ω _ _ s' hs' ↦ ?_⟩
  · exact (h₁ Ω z' hz').of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) z').app _).symm
  · obtain rfl : V = C.puncturedY := by
      ext1
      exact hV
    have := h₂ n
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
      (F := (DerivedCategory.homologyFunctor _ n).obj
        ((C.puncturedY.ι ≫ C.iY)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj
          (C.boundaryComplex Λ E)))
      ((DerivedCategory.homologyFunctor _ n).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) _).app _))
  · have hz' : C.z ∉ Set.range (s' ≫ C.iY) := by
      rintro ⟨w, hw⟩
      have hw' : s' w = s := by
        rw [← Set.mem_singleton_iff, ← hs']
        exact ⟨w, rfl⟩
      apply hsz
      rw [← hw']
      exact hw
    let e := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) iY).app
      (transverseBoundaryComplex hle E)
    have h := globalSectionsRestriction_naturality s' e.hom
    have h0 : globalSectionsRestriction s' ((iY)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj
        (transverseBoundaryComplex hle E)) = 0 :=
      globalSectionsRestriction_eq_zero_of_derived Λ s' _ (h₃ hYc Ω s' hz')
    rw [h0, zero_comp] at h
    rw [← cancel_epi ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map e.hom), h,
      comp_zero]

section Vanishing

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The restriction map along a composite `g ≫ f` vanishes as soon as the restriction along `f`
does. -/
lemma globalSectionsRestriction_comp_eq_zero {X₁ X₂ X₃ : Scheme.{u}} (f : X₂ ⟶ X₁)
    (g : X₃ ⟶ X₂) (K : DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (h : globalSectionsRestriction f K = 0) : globalSectionsRestriction (g ≫ f) K = 0 := by
  have hc := globalSectionsRestriction_comp f g K
  rw [h, zero_comp] at hc
  rwa [← cancel_mono ((rightDerivedGlobalSections A X₃).map
    ((Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar A f) (upperStar A g)).symm).hom.app K)),
    zero_comp]

/-- The restriction map along a composite `g ≫ f` vanishes as soon as the restriction along `g`
of the pullback vanishes. -/
lemma globalSectionsRestriction_comp_eq_zero_of_right {X₁ X₂ X₃ : Scheme.{u}} (f : X₂ ⟶ X₁)
    (g : X₃ ⟶ X₂) (K : DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (h : globalSectionsRestriction g (((f)^*[A]).mapDerivedCategory.obj K) = 0) :
    globalSectionsRestriction (g ≫ f) K = 0 := by
  have hc := globalSectionsRestriction_comp f g K
  rw [h, comp_zero] at hc
  rwa [← cancel_mono ((rightDerivedGlobalSections A X₃).map
    ((Functor.mapDerivedCategoryNatIso (upperStarComp A g f) ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar A f) (upperStar A g)).symm).hom.app K)),
    zero_comp]

/-- If the restriction along `f` followed by the restriction along `g` vanishes and the latter
is an isomorphism, the restriction along `f` vanishes. -/
lemma globalSectionsRestriction_eq_zero_of_comp {X₁ X₂ X₃ : Scheme.{u}} (f : X₂ ⟶ X₁)
    (g : X₃ ⟶ X₂) (K : DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    [IsIso (globalSectionsRestriction g (((f)^*[A]).mapDerivedCategory.obj K))]
    (h : globalSectionsRestriction (g ≫ f) K = 0) : globalSectionsRestriction f K = 0 := by
  have hc := globalSectionsRestriction_comp f g K
  rw [h, zero_comp] at hc
  rw [← cancel_mono (globalSectionsRestriction g (((f)^*[A]).mapDerivedCategory.obj K)),
    zero_comp, ← hc]

/-- Let `j : U ⟶ Z` be a morphism and `F` a complex on `U`. If the restriction of
`Rj_* F` along `ι ≫ j` vanishes, so does the restriction of `F` along `ι`: the restriction of
`Rj_* F` along `j` followed by the counit `j^* Rj_* F ⟶ F` is the Leray isomorphism
`RΓ(Z, Rj_* F) ≅ RΓ(U, F)` (`globalSectionsRestriction_comp_map_counit`). -/
lemma globalSectionsRestriction_eq_zero_of_lowerStar {U Z W : Scheme.{u}} (j : U ⟶ Z)
    (ι : W ⟶ U) (F : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (h : globalSectionsRestriction (ι ≫ j) (((j)_*[A]).rightDerivedFunctor.obj F) = 0) :
    globalSectionsRestriction ι F = 0 := by
  have hc := globalSectionsRestriction_comp j ι (((j)_*[A]).rightDerivedFunctor.obj F)
  rw [h, zero_comp] at hc
  have hn := globalSectionsRestriction_naturality ι
    ((mapDerivedUpperStarLowerStarAdjunction A j).counit.app F)
  have hl := globalSectionsRestriction_comp_map_counit j F
  dsimp only [Functor.id_obj] at hn
  rw [← cancel_epi ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A j).hom.app F),
    comp_zero, ← hl, Category.assoc, hn, ← Category.assoc]
  erw [← hc]
  rw [zero_comp]

end Vanishing

/-- Let `j : U ⟶ Z` be a morphism, `F` a complex on `U` and `M = Rj_* F`. If `ι : W ⟶ U` and
`ι ≫ j` factors through a morphism `c : S ⟶ Z` along which the restriction of `M` vanishes, then
the restriction of `F` along `ι` vanishes. -/
lemma globalSectionsRestriction_eq_zero_of_factor {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {U Z' S W : Scheme.{u}} (j : U ⟶ Z') (c : S ⟶ Z')
    (F : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (hc : globalSectionsRestriction c (((j)_*[A]).rightDerivedFunctor.obj F) = 0)
    (ι : W ⟶ U) (jW : W ⟶ S) (hι : ι ≫ j = jW ≫ c) : globalSectionsRestriction ι F = 0 := by
  have hjc := globalSectionsRestriction_comp_eq_zero c jW _ hc
  rw [← hι] at hjc
  exact globalSectionsRestriction_eq_zero_of_lowerStar _ _ _ hjc

/-- **Restriction to a strictly local scheme centred on the boundary vanishes** (blueprint
`lemma-restriction-punctured-curve--1` and the proof of `lemma-restriction-punctured-curve`,
with the stalk `M_s` computed on the strictly local scheme `S` instead of the strict localization
of `Z`). In the situation of the transverse boundary calculation
(`AlgebraicGeometry.Etale.transverseBoundary`) with `Y` connected, let `c : S = Spec R ⟶ Z` be a
morphism from a strictly local scheme whose closed point maps to a closed point `s` of `Y`. Then
the restriction map `RΓ(Z, M) ⟶ RΓ(S, c^* M)` is zero, `M = Rj_* i_! E`.

Indeed `RΓ(S, c^* M) ⟶ M_s` is an isomorphism (`S` is strictly local), so it suffices that the
restriction `RΓ(Z, M) ⟶ M_s` vanishes. If `s = z` its target `M_z` is zero; otherwise it factors
through the restriction `RΓ(Y, M|_Y) ⟶ M_s`, which is zero by the transverse boundary
calculation. -/
theorem globalSectionsRestriction_transverseBoundaryComplex_eq_zero (hℓ : (ℓ : k) ≠ 0)
    (hΛ : IsNilpotent (ℓ : Λ)) (hZ : IsEtaleLimitOfSmoothSurfaces Z)
    [IsLocallyNoetherian Z.left] [IsRegular Z.left] (hX : IsRegularDivisor iX)
    (hY : IsRegularDivisor iY) (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX))
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) [ConnectedSpace Y] {R : Type u} [CommRing R]
    [IsStrictlyHenselianLocalRing R] (c : Spec (.of R) ⟶ Z.left) (s : Y)
    (hs : IsClosed ({s} : Set Y)) (hcs : c (IsLocalRing.closedPoint R) = iY s) :
    globalSectionsRestriction c (transverseBoundaryComplex hle E) = 0 := by
  obtain ⟨h₁, -, h₃⟩ := transverseBoundary hℓ hΛ hZ hX hY z hz hXY hUY hUXY hle E hE
  have := hY.isClosedImmersion
  let t := Scheme.closedGeometricPoint R
  have ht : Set.range (t ≫ c) = {iY s} := by
    ext w
    refine ⟨?_, fun hw ↦ ⟨IsLocalRing.closedPoint _, ?_⟩⟩
    · rintro ⟨a, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.closedGeometricPoint_apply, hcs]
      rfl
    · rw [Set.mem_singleton_iff.1 hw, Scheme.Hom.comp_apply, Scheme.closedGeometricPoint_apply,
        hcs]
  have : IsIso (globalSectionsRestriction t
      (((c)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (transverseBoundaryComplex hle E))) :=
    isIso_globalSectionsRestriction_closedGeometricPoint R _
  refine globalSectionsRestriction_eq_zero_of_comp c t _ ?_
  by_cases hsz : iY s = z
  · exact (Functor.map_isZero _ (h₁ _ (t ≫ c) (ht.trans (by rw [hsz])))).eq_of_tgt _ _
  · have hsub : Set.range (t ≫ c) ⊆ Set.range iY := by
      rw [ht]
      rintro _ rfl
      exact ⟨s, rfl⟩
    have hker : iY.ker ≤ (t ≫ c).ker := by
      rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support, Scheme.Hom.support_ker,
        iY.isClosedMap.isClosed_range.closure_eq]
      exact hsub
    have hfac := IsClosedImmersion.lift_fac iY (t ≫ c) hker
    rw [← hfac]
    refine globalSectionsRestriction_comp_eq_zero_of_right _ _ _
      (h₃ ‹_› s hs hsz _ _ ?_)
    have hinj : Function.Injective iY := iY.isClosedEmbedding.injective
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      apply hinj
      rw [← Scheme.Hom.comp_apply, hfac, ← Set.mem_singleton_iff, ← ht]
      exact ⟨a, rfl⟩
    · intro hy
      rw [Set.mem_singleton_iff.1 hy]
      obtain ⟨a, ha⟩ : iY s ∈ Set.range (t ≫ c) := by rw [ht]; rfl
      refine ⟨a, hinj ?_⟩
      rw [← Scheme.Hom.comp_apply, hfac, ha]

/-- **Restriction through a strictly local scheme vanishes**: in the situation of
`globalSectionsRestriction_transverseBoundaryComplex_eq_zero`, for every `ι : W ⟶ Z - Y` such
that `W ⟶ Z - Y ⟶ Z` factors through `c : S ⟶ Z`, the restriction map
`RΓ(Z - Y, i_! E) ⟶ RΓ(W, ι^* i_! E)` is zero: it factors as
`RΓ(Z - Y, i_! E) = RΓ(Z, M) ⟶ RΓ(S, c^* M) ⟶ RΓ(W, ...)`. -/
theorem globalSectionsRestriction_eq_zero_of_strictlyLocal (hℓ : (ℓ : k) ≠ 0)
    (hΛ : IsNilpotent (ℓ : Λ)) (hZ : IsEtaleLimitOfSmoothSurfaces Z)
    [IsLocallyNoetherian Z.left] [IsRegular Z.left] (hX : IsRegularDivisor iX)
    (hY : IsRegularDivisor iY) (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX))
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) [ConnectedSpace Y] {R : Type u} [CommRing R]
    [IsStrictlyHenselianLocalRing R] (c : Spec (.of R) ⟶ Z.left) (s : Y)
    (hs : IsClosed ({s} : Set Y)) (hcs : c (IsLocalRing.closedPoint R) = iY s) {W : Scheme.{u}}
    (ι : W ⟶ UY.toScheme) (jW : W ⟶ Spec (.of R)) (hι : ι ≫ UY.ι = jW ≫ c) :
    globalSectionsRestriction ι
      (((Z.left.homOfLE hle)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) = 0 :=
  globalSectionsRestriction_eq_zero_of_factor UY.ι c _
    (globalSectionsRestriction_transverseBoundaryComplex_eq_zero hℓ hΛ hZ hX hY z hz hXY hUY
      hUXY hle E hE c s hs hcs) ι jW hι

section Punctured

variable {C : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The punctured strict localization `C_(s) - s`: the complement of the closed point in the
strict localization of `C` at the geometric point `s`. -/
noncomputable def puncturedStrictLocalization (s' : Spec (.of Ω) ⟶ C) :
    (Scheme.strictLocalization s').Opens :=
  ⟨{IsLocalRing.closedPoint (Scheme.strictHenselization s')}ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩

omit [IsAlgClosed k] in
/-- Let `C ⊆ Z` be closed with `C ∩ Y = {s}` and `s'` a geometric point of `C` over `s`. Then the
punctured strict localization `C_(s) - s` maps into `Z - Y`. -/
lemma range_puncturedStrictLocalization_subset (iC : C ⟶ Z.left) [IsClosedImmersion iC] (s : Y)
    (hCY : Set.range iC ∩ Set.range iY = {iY s}) (s' : Spec (.of Ω) ⟶ C)
    (hs' : iC (s' (IsLocalRing.closedPoint Ω)) = iY s)
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ) :
    Set.range ((puncturedStrictLocalization s').ι ≫ Scheme.strictLocalizationToBase s' ≫ iC) ⊆
      Set.range UY.ι := by
  rintro _ ⟨q, rfl⟩
  rw [Scheme.Opens.range_ι, hUY]
  rintro ⟨y, hy⟩
  have hq : q.val ≠ IsLocalRing.closedPoint (Scheme.strictHenselization s') := q.2
  apply Scheme.strictLocalizationToBase_ne_of_ne_closedPoint s' _ hq
  have hmem : iC (Scheme.strictLocalizationToBase s' q.val) ∈ Set.range iC ∩ Set.range iY := by
    refine ⟨⟨_, rfl⟩, ⟨y, ?_⟩⟩
    rw [hy]
    rfl
  rw [hCY, Set.mem_singleton_iff, ← hs'] at hmem
  exact iC.isClosedEmbedding.injective hmem

/-- The map `C_(s) - s ⟶ Z - Y` from the punctured strict localization of a closed subscheme
`C ⊆ Z` with `C ∩ Y = {s}` at a geometric point over `s`. -/
noncomputable def puncturedStrictLocalizationMap (iC : C ⟶ Z.left) [IsClosedImmersion iC] (s : Y)
    (hCY : Set.range iC ∩ Set.range iY = {iY s}) (s' : Spec (.of Ω) ⟶ C)
    (hs' : iC (s' (IsLocalRing.closedPoint Ω)) = iY s)
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ) :
    (puncturedStrictLocalization s').toScheme ⟶ UY.toScheme :=
  IsOpenImmersion.lift UY.ι _ (range_puncturedStrictLocalization_subset iC s hCY s' hs' hUY)

/-- **Restriction to a transverse punctured curve**
(blueprint `lemma-restriction-punctured-curve`). In the situation of the transverse boundary
calculation (`AlgebraicGeometry.Etale.transverseBoundary`) with `Y` connected, let `C ⊆ Z` be a
closed subscheme (in the blueprint a curve) with `C ∩ Y = {s}`, and let `C_(s)` be its strict
localization at a geometric point over `s`. Then the restriction map
```
RΓ(Z - Y, i_! E) ⟶ RΓ(C_(s) - s, (i_! E)|_{C_(s) - s})
```
is zero. This is `AlgebraicGeometry.Etale.globalSectionsRestriction_eq_zero_of_strictlyLocal` for
the strictly local scheme `C_(s)`, whose closed point maps to `s`; the point `s` is closed in `Y`,
being cut out by the closed subscheme `C`. -/
theorem puncturedRestriction_eq_zero (hℓ : (ℓ : k) ≠ 0) (hΛ : IsNilpotent (ℓ : Λ))
    (hZ : IsEtaleLimitOfSmoothSurfaces Z) [IsLocallyNoetherian Z.left] [IsRegular Z.left]
    (hX : IsRegularDivisor iX) (hY : IsRegularDivisor iY)
    (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX))
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) [ConnectedSpace Y] (iC : C ⟶ Z.left) [IsClosedImmersion iC]
    (s : Y) (hCY : Set.range iC ∩ Set.range iY = {iY s}) (s' : Spec (.of Ω) ⟶ C)
    (hs' : iC (s' (IsLocalRing.closedPoint Ω)) = iY s) :
    globalSectionsRestriction (puncturedStrictLocalizationMap iC s hCY s' hs' hUY)
      (((Z.left.homOfLE hle)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) = 0 := by
  have := hY.isClosedImmersion
  have hs : IsClosed ({s} : Set Y) := by
    have hcl : IsClosed (Set.range iC ∩ Set.range iY) :=
      iC.isClosedEmbedding.isClosed_range.inter iY.isClosedEmbedding.isClosed_range
    rw [hCY] at hcl
    have h := hcl.preimage iY.base.hom.continuous
    rwa [show (iY.base ⁻¹' {iY s} : Set Y) = {s} from
      Set.ext fun y ↦ ⟨fun hy ↦ iY.isClosedEmbedding.injective hy, fun hy ↦ by rw [hy]; rfl⟩] at h
  have := Scheme.isStrictlyHenselianLocalRing_strictHenselization s'
  refine globalSectionsRestriction_eq_zero_of_strictlyLocal (R := Scheme.strictHenselization s')
    hℓ hΛ hZ hX hY z hz hXY hUY hUXY hle E hE
    (Scheme.strictLocalizationToBase s' ≫ iC) s hs ?_ _ (puncturedStrictLocalization s').ι ?_
  · rw [Scheme.Hom.comp_apply, ← hs']
    congr 1
    have h := congrArg (fun φ ↦ φ (IsLocalRing.closedPoint Ω))
      (Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase s')
    dsimp only at h
    rw [← h, Scheme.Hom.comp_apply]
    congr 1
    refine (PrimeSpectrum.ext ?_).symm
    change Ideal.comap (Scheme.strictHenselizationEval s').hom (IsLocalRing.maximalIdeal Ω) =
      IsLocalRing.maximalIdeal _
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
      Scheme.maximalIdeal_strictHenselization]
  · exact IsOpenImmersion.lift_fac _ _ _

end Punctured

end AlgebraicGeometry.Etale
