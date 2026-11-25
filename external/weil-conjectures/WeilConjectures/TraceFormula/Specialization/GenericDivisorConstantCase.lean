/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DVRStalkLocalEquation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorGenericPoint
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorThickOrigin

/-!

# The constant case of the codimension-one core, locally

Let `Z = V(I) ⊆ X`, `j : X ∖ Z ⟶ X` the complement and `ζ` a point of `Z`. Suppose that `ζ` has an
open neighbourhood `W` in `X` with a smooth morphism `f : W ⟶ 𝔸¹_k` such that `Z ∩ W = f⁻¹ V(x^m)`
(as closed subschemes) for some `m ≥ 1`, and let `L` be a complex on `X` whose restriction to `W`
is isomorphic to that of `j_! ℚ̄_ℓ`. Then the defect `C_{W, Z ∩ W}(L|_W)` vanishes
(`ProEtale.CondensedRing.isZero_specializationDefect_upperStar_of_smooth`): by the smooth exchange
for the open immersion `W ⟶ X`, the defect does not see the difference between `j_! ℚ̄_ℓ` and
`ℚ̄_ℓ`, and `C_{W, Z ∩ W}(ℚ̄_ℓ) = 0` by the smooth exchange along `f` and the thick origin.

Consequently, for an extension by zero `j_! N` which is constant on `W ∖ Z`, the restricted
specialization `Le^* Ψ_X(j_! N)` vanishes near `ζ`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_of_smooth`). This is the
codimension-one core `exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range` in the
special case of constant coefficients near a point where the divisor is a multiple of a smooth
divisor.

For a lisse generator `N ≅ Rg_! Rj'_! M` with `M ≅ ℚ̄_ℓ` and `W ∖ Z` contained in the image of
`U₀`, the restrictions of `j_! N` and `j_! ℚ̄_ℓ` to `W` agree
(`ProEtale.CondensedRing.nonempty_upperStar_lowerShriek_iso_unit_of_subset_range`): over `W ∖ Z`
the immersion `U₀ ⟶ X ∖ Z` restricts to an isomorphism, being a surjective immersion onto a
reduced scheme. This gives the core for `M ≅ ℚ̄_ℓ` near a point with a smooth chart
(`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range_of_unit`), and, using that
`𝒪_{X,ζ}` is a discrete valuation ring, near a point where some smooth `f₀ : W₀ ⟶ 𝔸¹_k` pulls the
coordinate back to a uniformizer of `𝒪_{X,ζ}`
(`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range_of_uniformizer`).

## Not covered

* The existence of such a smooth uniformizer near `ζ` (`X` and `Z_red` smooth near `ζ`): it needs
  `k` perfect (generic smoothness of normal varieties) and the fibrewise criterion of smoothness.
* Non-constant lisse `M` (finite étale trivialisation, normalisation and proper exchange).

The vanishing of the thick origin,
`isZero_specializationDefect_polyAffineThickOrigin_unit_padicAlgCl`, is proved in another
subsection.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The defect near a smooth multiple divisor, for complexes locally isomorphic to
`j_! ℚ̄_ℓ`**: let `W` be an open of `X` with a smooth `f : W ⟶ 𝔸¹_k` such that
`Z ∩ W = f⁻¹ V(x^m)`, `m ≥ 1`, and let `L` be a complex on `X` with `L|_W ≅ (j_! ℚ̄_ℓ)|_W` for
the complement `j : X ∖ Z ⟶ X`. Then `C_{W, Z ∩ W}(L|_W) = 0`. Indeed, by the smooth exchange for
the open immersion `g : W ⟶ X`,
`C_W(g^* j_! ℚ̄_ℓ) ≅ g_Z^* C_X(j_! ℚ̄_ℓ) ≅ g_Z^* C_X(ℚ̄_ℓ) ≅ C_W(ℚ̄_ℓ)`,
which vanishes by the smooth exchange along `f` and the thick origin. -/
theorem isZero_specializationDefect_upperStar_of_smooth (I : X.left.IdealSheafData)
    (W : X.left.Opens) (f : overRestrict X W ⟶ polyAffine k 1) [Smooth f.left] {m : ℕ}
    (hm : 0 < m)
    (hI : I.comap (overRestrictι X W).left = (polyAffineThickOrigin k m).comap f.left)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X W)).obj L ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (overRestrictι X W)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (overRestrictι X I.support.compl)).obj (𝟙_ _)))) :
    IsZero (specializationDefect (overRestrict X W) (I.comap (overRestrictι X W).left) k'
      (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X W)).obj L).obj) := by
  have h₀ := isZero_specializationDefect_unit_of_smooth k' f (polyAffineThickOrigin k m)
    (isZero_specializationDefect_polyAffineThickOrigin_unit_padicAlgCl (ℓ := ℓ) k' hm)
  rw [← hI] at h₀
  obtain ⟨e₁⟩ := nonempty_specializationDefect_iso (overRestrict X W)
    (I.comap (overRestrictι X W).left) k' (Profinite.padicAlgClRingObj ℓ)
    ((boundedConstructible _).ι.mapIso e)
  obtain ⟨e₂⟩ := nonempty_specializationDefect_upperStar_iso (overRestrictι X W) I k'
    ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictι X I.support.compl)).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X I.support.compl)).obj (𝟙_ _)))
  obtain ⟨e₃⟩ := nonempty_specializationDefect_lowerShriek_upperStar_iso X I k'
    (overRestrictι X I.support.compl) (isCompl_range_overRestrictι_centreι I)
    (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  obtain ⟨e₄⟩ := nonempty_specializationDefect_upperStar_iso (overRestrictι X W) I k'
    (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  obtain ⟨e₅⟩ := nonempty_specializationDefect_iso (overRestrict X W)
    (I.comap (overRestrictι X W).left) k' (Profinite.padicAlgClRingObj ℓ)
    (leftDerivedUpperStarUnitIso _ (overRestrictι X W).left)
  exact h₀.of_iso (e₁ ≪≫ e₂ ≪≫ Functor.mapIso _ e₃ ≪≫ e₄.symm ≪≫ e₅)

/-- **The codimension-one core for constant coefficients near a smooth multiple divisor**: let `ζ`
be a point of `Z = V(I)` with an open neighbourhood `W` in `X` and a smooth `f : W ⟶ 𝔸¹_k` such
that `Z ∩ W = f⁻¹ V(x^m)`, `m ≥ 1`, and let `N` be a complex on `X ∖ Z` such that `j_! N` and
`j_! ℚ̄_ℓ` have isomorphic restrictions to `W`. Then `Le^* Ψ_X(j_! N)` vanishes near `ζ`: the
defect `C_{W, Z ∩ W}((j_! N)|_W)` vanishes (`isZero_specializationDefect_upperStar_of_smooth`),
vanishing near a point is local on `X`, and the defect of `j_! N` is `Le^* Ψ_X(j_! N)[1]`. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_smooth (I : X.left.IdealSheafData)
    (ζ : (centre X I).left) (W : X.left.Opens) (hζW : I.subschemeι ζ ∈ W)
    (f : overRestrict X W ⟶ polyAffine k 1) [Smooth f.left] {m : ℕ} (hm : 0 < m)
    (hI : I.comap (overRestrictι X W).left = (polyAffineThickOrigin k m).comap f.left)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X W)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj N) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (overRestrictι X W)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (overRestrictι X I.support.compl)).obj (𝟙_ _)))) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  have hζ : ζ ∈ Set.range (centreMap (overRestrictι X W) I).left := by
    rw [range_centreMap, Set.mem_preimage, range_overRestrictι]
    exact hζW
  obtain ⟨ζ', rfl⟩ := hζ
  have hL := isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ
    (overRestrictι X I.support.compl) (centreι X I)
    (isCompl_range_overRestrictι_centreι I).disjoint N
  have hΨ := NearbyCyclesModel.isZero_nearbyCycles_obj (Profinite.padicAlgClRingObj ℓ)
    (deformationModel (centre X I) ⊥ k')
    (((boundedConstructible _).ι.map_isZero hL).of_iso
      ((boundedConstructibleUpperStarCompatibility _ ℓ (centreι X I)).symm.app _))
  obtain ⟨U, hζU, hU⟩ := defectVanishesNear_of_isOpenImmersion I k' (overRestrictι X W) _ ζ'
    ⟨⊤, trivial, Functor.map_isZero _
      (isZero_specializationDefect_upperStar_of_smooth k' I W f hm hI _ e)⟩
  exact ⟨U, hζU, isZero_restrict_of_isZero_restrict_specializationDefect X I k' _ _ _ hΨ hU⟩

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### Lisse generators which are constant near `ζ` -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Restriction

variable {k : Type u} [Field k] {S T : Over (Spec (.of k))}

/-- The restriction `c⁻¹ U ⟶ U` of a morphism `c : S ⟶ T` over an open `U` of `T`, as a morphism
of `Over (Spec k)`. -/
noncomputable def overRestrictMap (c : S ⟶ T) (U : T.left.Opens) :
    overRestrict S (c.left ⁻¹ᵁ U) ⟶ overRestrict T U :=
  Over.homMk (c.left ∣_ U) (by simp [morphismRestrict_ι_assoc, Over.w])

/-- The restriction of `c : S ⟶ T` over an open `U` of `T` is a base change of `c`. -/
lemma isPullback_overRestrictMap (c : S ⟶ T) (U : T.left.Opens) :
    IsPullback (overRestrictι S (c.left ⁻¹ᵁ U)) (overRestrictMap c U) c (overRestrictι T U) := by
  have w : overRestrictι S (c.left ⁻¹ᵁ U) ≫ c = overRestrictMap c U ≫ overRestrictι T U := by
    ext1
    exact (morphismRestrict_ι _ _).symm
  exact IsPullback.of_map (Over.forget _) w (isPullback_morphismRestrict c.left U).flip

/-- The restriction of an immersion `c : S ⟶ T` over an open `U` of `T` contained in its image is
an isomorphism, provided that `U` is reduced. -/
lemma isIso_overRestrictMap (c : S ⟶ T) [IsImmersion c.left] (U : T.left.Opens)
    [IsReduced U.toScheme] (hc : (U : Set T.left) ⊆ Set.range c.left.base) :
    IsIso (overRestrictMap c U) := by
  have : IsIso (c.left ∣_ U) := by
    refine isIso_of_isImmersion_of_surjective _ fun y ↦ ?_
    obtain ⟨x, hx⟩ := hc y.2
    refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
    · rw [Scheme.Hom.mem_preimage, hx]
      exact y.2
    · rw [morphismRestrict_base_coe]
      exact hx
  have : IsIso ((Over.forget _).map (overRestrictMap c U)) := this
  exact isIso_of_reflects_iso _ (Over.forget _)

end Restriction

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- For an isomorphism `c`, `Rc_! (Lc^* K) ≅ K`: `Rc_! ≅ Rc_*`, and the unit `K ⟶ Rc_* Lc^* K`
is invertible since `Lc^*` is an equivalence. -/
lemma nonempty_lowerShriek_upperStar_iso_of_isIso {S T : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (c : S ⟶ T) [IsIso c]
    (K : Dᵇc(T.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((boundedConstructibleLowerShriek ℓ c).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c).obj K) ≅ K) := by
  have : IsIso c.left := (Over.forget _).map_isIso c
  exact ⟨(boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c).app _ ≪≫
    (asIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ c).unit.app K)).symm⟩

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **Restrictions of extensions by zero**: for the complement `j : X ∖ Z ⟶ X` and an open `W` of
`X`, complexes `A`, `B` on `X ∖ Z` with isomorphic restrictions to `W ∖ Z` have extensions by zero
`j_! A`, `j_! B` with isomorphic restrictions to `W` (base change of `j_!`). -/
lemma nonempty_upperStar_openImmersionLowerShriek_iso {I : X.left.IdealSheafData}
    (W : X.left.Opens)
    (A B : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι (overRestrict X I.support.compl)
          ((overRestrictι X I.support.compl).left ⁻¹ᵁ W))).obj A ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι (overRestrict X I.support.compl)
          ((overRestrictι X I.support.compl).left ⁻¹ᵁ W))).obj B) :
    Nonempty ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X W)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj A) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (overRestrictι X W)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj B)) := by
  have sq := (isPullback_overRestrictInterι I.support.compl W).flip
  exact ⟨(boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
      (Profinite.padicAlgClRingObj ℓ) ℓ sq).app A ≪≫
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictInterι I.support.compl W)).mapIso e ≪≫
    ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
      (Profinite.padicAlgClRingObj ℓ) ℓ sq).app B).symm⟩

/-- **A lisse generator with constant coefficients is constant where it is lisse**: let
`g : Z₀ ⟶ X ∖ Z` be a closed immersion, `j' : U₀ ⟶ Z₀` an open immersion, `N ≅ Rg_! Rj'_! M` with
`M ≅ ℚ̄_ℓ`, and `W` an open of the reduced scheme `X` such that `W ∖ Z` is contained in the image
of `U₀`. Then `j_! N` and `j_! ℚ̄_ℓ` have isomorphic restrictions to `W`. Indeed, over `W ∖ Z` the
immersion `c = g ∘ j'` restricts to a surjective immersion onto a reduced scheme, hence to an
isomorphism `c_W`, and `(Rc_! M)|_{W ∖ Z} ≅ Rc_{W!} (M|_{c⁻¹(W ∖ Z)}) ≅ Rc_{W!} Lc_W^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
by base change. -/
theorem nonempty_upperStar_lowerShriek_iso_unit_of_subset_range [IsReduced X.left]
    {I : X.left.IdealSheafData}
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hM : Nonempty (M ≅ 𝟙_ _))
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (W : X.left.Opens)
    (hW : (W : Set X.left) ∩ (I.support.compl : Set X.left) ⊆
      Set.range (j' ≫ g ≫ overRestrictι X I.support.compl).left.base) :
    Nonempty ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X W)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj N) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (overRestrictι X W)).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (overRestrictι X I.support.compl)).obj (𝟙_ _)))) := by
  obtain ⟨eM⟩ := hM
  set ι := overRestrictι X I.support.compl
  set U : (overRestrict X I.support.compl).left.Opens := ι.left ⁻¹ᵁ W
  set c := j' ≫ g
  have : IsImmersion c.left := by
    rw [Over.comp_left]
    infer_instance
  have hcU : (U : Set (overRestrict X I.support.compl).left) ⊆ Set.range c.left.base := by
    intro y hy
    obtain ⟨x, hx⟩ := hW ⟨hy, by
      rw [← range_overRestrictι X I.support.compl]
      exact ⟨y, rfl⟩⟩
    refine ⟨x, ι.left.isOpenEmbedding.injective ?_⟩
    rw [← hx]
    simp [c]
  have : IsReduced (overRestrict X I.support.compl).left :=
    inferInstanceAs (IsReduced (I.support.compl : X.left.Opens))
  have := isIso_overRestrictMap c U hcU
  have hbc := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (isPullback_overRestrictMap c U)
  obtain ⟨eU⟩ := nonempty_lowerShriek_upperStar_iso_of_isIso (ℓ := ℓ) (overRestrictMap c U) (𝟙_ _)
  refine nonempty_upperStar_openImmersionLowerShriek_iso W _ _ ?_
  exact (boundedConstructibleUpperStar _ ℓ (overRestrictι _ U)).mapIso
      (e ≪≫ ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j' g).app M).symm) ≪≫
    asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (isPullback_overRestrictMap c U)).app M) ≪≫
    (boundedConstructibleLowerShriek ℓ (overRestrictMap c U)).mapIso
      ((boundedConstructibleUpperStar _ ℓ (overRestrictι U₀ (c.left ⁻¹ᵁ U))).mapIso eM ≪≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ _)).symm ≪≫
        Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (overRestrictMap c U))) ≪≫
    eU ≪≫ Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (overRestrictι _ U)) ≪≫
    (boundedConstructibleUpperStar _ ℓ (overRestrictι _ U)).mapIso
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ ι))

/-- **The codimension-one core for constant coefficients near a smooth multiple divisor** (route
(i) of `exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range`, blueprint
`lemma-vanishing-generic-points-principal-divisor`): the hypotheses of the core with `X` reduced,
`M ≅ ℚ̄_ℓ`, and an open neighbourhood `W ⊆ V` of `ζ` with a smooth `f : W ⟶ 𝔸¹_k` such that
`Z ∩ W = f⁻¹ V(x^m)`, `m ≥ 1`. Then `Le^* Ψ_X(j_! N)` vanishes near `ζ`: `j_! N` and `j_! ℚ̄_ℓ`
agree on `W` (`nonempty_upperStar_lowerShriek_iso_unit_of_subset_range`), and the constant case is
`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_smooth`. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range_of_unit
    (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] [IsReduced X.left] {I : X.left.IdealSheafData}
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hM : Nonempty (M ≅ 𝟙_ _))
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) (V : X.left.Opens)
    (hV : (V : Set X.left) ∩ (I.support.compl : Set X.left) ⊆
      Set.range (j' ≫ g ≫ overRestrictι X I.support.compl).left.base)
    (W : X.left.Opens) (hWV : W ≤ V) (hζW : I.subschemeι ζ ∈ W)
    (f : overRestrict X W ⟶ polyAffine k 1) [Smooth f.left] {m : ℕ} (hm : 0 < m)
    (hI : I.comap (overRestrictι X W).left = (polyAffineThickOrigin k m).comap f.left) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  obtain ⟨eW⟩ := nonempty_upperStar_lowerShriek_iso_unit_of_subset_range g j' M hM N e W
    fun _ hx ↦ hV ⟨hWV hx.1, hx.2⟩
  exact exists_isZero_upperStar_nearbyCycles_lowerShriek_of_smooth k' I ζ W hζW f hm hI N eW

/-- **The codimension-one core for constant coefficients near a smooth uniformizer** (route (i)
of `exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range`, blueprint
`lemma-vanishing-generic-points-principal-divisor`): the hypotheses of the core with `M ≅ ℚ̄_ℓ`,
together with an open neighbourhood `W₀ ⊆ V` of `ζ` and a smooth `f₀ : W₀ ⟶ 𝔸¹_k` such that `f₀^* x`
is a uniformizer of the discrete valuation ring `𝒪_{X,ζ}`. Then `Le^* Ψ_X(j_! N)` vanishes near `ζ`.
Indeed, on a smaller neighbourhood `W` of `ζ`, `h = (unit) · (f₀^* x)^m` with `m ≥ 1`
(`Scheme.exists_span_eq_span_pow_of_irreducible_germ`), so `Z ∩ W = f⁻¹ V(x^m)` for the
restriction `f` of `f₀` to `W`, and
`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range_of_unit` applies. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range_of_uniformizer
    (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0)
    {I : X.left.IdealSheafData} (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hM : Nonempty (M ≅ 𝟙_ _))
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (V : X.left.Opens)
    (hV : (V : Set X.left) ∩ (I.support.compl : Set X.left) ⊆
      Set.range (j' ≫ g ≫ overRestrictι X I.support.compl).left.base)
    (W₀ : X.left.Opens) (hW₀V : W₀ ≤ V) (hζW₀ : I.subschemeι ζ ∈ W₀)
    (f₀ : overRestrict X W₀ ⟶ polyAffine k 1) [Smooth f₀.left]
    (hf₀ : Irreducible (X.left.presheaf.germ (W₀.ι ''ᵁ ⊤) (I.subschemeι ζ)
      ⟨⟨I.subschemeι ζ, hζW₀⟩, trivial, rfl⟩
      (f₀.left.appTop (polyAffineCoord k (Fin.last 0))))) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  have := hX.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have := (hX.2 (I.subschemeι ζ)).1
  have := (hX.2 (I.subschemeι ζ)).2
  have : IsDiscreteValuationRing (X.left.presheaf.stalk (I.subschemeι ζ)) :=
    IsDiscreteValuationRing.of_maximalIdeal_mem_minimalPrimes_span_singleton
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral X.left (U := ⊤) _ trivial)).2 hh)
      (maximalIdeal_stalk_mem_minimalPrimes (subschemeι_mem_zeroLocus hI ζ)
        (eq_of_specializes_subschemeι hI ζ hζ))
  have hxU₀ : I.subschemeι ζ ∈ W₀.ι ''ᵁ ⊤ := ⟨⟨I.subschemeι ζ, hζW₀⟩, trivial, rfl⟩
  have hgerm : X.left.presheaf.germ (W₀.ι ''ᵁ ⊤) _ hxU₀
      (X.left.presheaf.map (homOfLE le_top : W₀.ι ''ᵁ ⊤ ⟶ ⊤).op h) =
      X.left.presheaf.germ ⊤ (I.subschemeι ζ) trivial h :=
    X.left.presheaf.germ_res_apply _ _ _ _
  obtain ⟨W, hζW, iW, m, hm, hspan⟩ := Scheme.exists_span_eq_span_pow_of_irreducible_germ hxU₀
    (X.left.presheaf.map (homOfLE le_top : W₀.ι ''ᵁ ⊤ ⟶ ⊤).op h)
    (f₀.left.appTop (polyAffineCoord k (Fin.last 0)))
    (by
      rw [hgerm]
      exact (map_ne_zero_iff _ (germ_injective_of_isIntegral X.left (U := ⊤) _ trivial)).2 hh)
    hf₀
    (by
      rw [hgerm, ← Scheme.mem_basicOpen]
      exact (X.left.mem_zeroLocus_iff _ _).1 (subschemeι_mem_zeroLocus hI ζ) h rfl)
  have hWW₀ : W ≤ W₀ := (leOfHom iW).trans (W₀.ι_image_le _)
  let r : overRestrict X W ⟶ overRestrict X W₀ := Over.homMk (X.left.homOfLE hWW₀) (by simp)
  have hr : r.left = X.left.homOfLE hWW₀ := rfl
  let f : overRestrict X W ⟶ polyAffine k 1 := r ≫ f₀
  have : Smooth f.left := by
    rw [Over.comp_left, hr]
    infer_instance
  refine exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range_of_unit k' g j' M hM N
    e ζ V hV W (hWW₀.trans hW₀V) hζW f hm ?_
  have hspan' := congrArg (Ideal.map (X.left.presheaf.map
    (homOfLE (W.ι_image_le ⊤) : W.ι ''ᵁ ⊤ ⟶ W).op).hom) hspan
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow]
    at hspan'
  rw [hI, IdealSheafData.comap_ofIdealTop, polyAffineThickOrigin, IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow]
  have e₁ : (overRestrictι X W).left.appTop h = X.left.presheaf.map
      (homOfLE (W.ι_image_le ⊤) : W.ι ''ᵁ ⊤ ⟶ W).op (X.left.presheaf.map iW.op
        (X.left.presheaf.map (homOfLE le_top : W₀.ι ''ᵁ ⊤ ⟶ ⊤).op h)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  have e₂ : f.left.appTop (polyAffineCoord k (Fin.last 0)) = X.left.presheaf.map
      (homOfLE (W.ι_image_le ⊤) : W.ι ''ᵁ ⊤ ⟶ W).op (X.left.presheaf.map iW.op
        (f₀.left.appTop (polyAffineCoord k (Fin.last 0)))) := by
    rw [Over.comp_left, hr, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.homOfLE_appTop, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp]
    rfl
  rw [e₁, e₂]
  exact congrArg _ hspan'

end AlgebraicGeometry.ProEtale.CondensedRing
