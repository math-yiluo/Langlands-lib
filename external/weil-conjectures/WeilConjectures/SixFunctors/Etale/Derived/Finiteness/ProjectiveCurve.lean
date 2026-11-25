/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
public import WeilConjectures.AlgebraicGeometry.Curve.GenericModel
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BettiCardinalities
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CurveModel
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.GenericConstructibility
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.GeometricFibreStalk
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal

/-!
# Constant coefficients on projective families of curves

Let `f : X ⟶ S` be a projective morphism of finite-type schemes over a field whose geometric
fibres have dimension at most one. The higher direct images `Rᵠf_* M` of a constant sheaf with
finite value `M` of order invertible on `S` are constructible. This is the curve case of the
constructibility of proper direct images (`proposition-proper-direct-image-finite-coefficients`).

The case of a smooth projective family of curves comes first: there the stalks of `Rᵠf_* 𝔽_ℓ`
are the cohomology groups of the geometric fibres, whose cardinalities `ℓ^c`, `ℓ^{2g}`, `ℓ^c`
are constructible functions of the base point by coherent base change
(`proposition-proper-direct-image-finite-coefficients`).
The general case is reduced to it by a generic curve model
(`proposition-proper-direct-image-finite-coefficients`), Noetherian induction and a filtration of
`M` (`proposition-proper-direct-image-finite-coefficients`).

## Main statements

- `AlgebraicGeometry.Etale.natCard_sheafH_constantZMod_geometricFibre`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod`
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {X S : Scheme.{u}}

/-- If a function `φ : S → ℕ` has constructible fibres, then for `a ≥ 2` every level set of
`s ↦ a ^ φ s` is constructible: it is the finite union of the fibres of `φ` over the exponents
`m` with `a ^ m = n`. -/
lemma isConstructible_setOf_pow_eq {T : Type*} [TopologicalSpace T] (φ : T → ℕ)
    (hφ : ∀ m : ℕ, Topology.IsConstructible (φ ⁻¹' {m})) {a : ℕ} (ha : 2 ≤ a) (n : ℕ) :
    Topology.IsConstructible {s | a ^ φ s = n} := by
  have h : {s | a ^ φ s = n} = ⋃ m ∈ {m : ℕ | a ^ m = n}, φ ⁻¹' {m} := by
    ext s
    simp
  rw [h]
  refine Topology.IsConstructible.biUnion ((Set.finite_Iic n).subset fun m hm ↦ ?_)
    fun m _ ↦ hφ m
  rw [Set.mem_ofPred_eq] at hm
  rw [Set.mem_Iic, ← hm]
  exact (Nat.lt_pow_self (by lia)).le

/-- A prime `ℓ` with `ℤ/ℓ` of invertible exponent on `S` is invertible on `S`. -/
lemma isUnit_natCast_of_hasInvertibleExponent_zmod (ℓ : ℕ)
    [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] : IsUnit (ℓ : Γ(S, ⊤)) := by
  obtain ⟨N, -, hN, hu⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := ULift.{u + 1} (ZMod ℓ)) (X := S)
  have hdvd : ℓ ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    simpa using congrArg ULift.down hN
  obtain ⟨d, rfl⟩ := hdvd
  rw [Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Betti cardinalities in a smooth
projective curve family.

Let `S` be Noetherian, `f : X ⟶ S` smooth of relative dimension one and projective
(`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), and `ℓ` a prime invertible on `S`. For a
point `s` of `S` let `X_{s̄} = X ×_S Spec κ(s)‾` be the geometric fibre, `c_s` the number of its
connected components and `g_s = dim H¹(X_{s̄}, 𝒪)` its arithmetic genus, which is the sum of the
genera of its connected components (each an integral smooth proper curve). Then
`|H⁰(X_{s̄}, 𝔽_ℓ)| = |H²(X_{s̄}, 𝔽_ℓ)| = ℓ^{c_s}`, `|H¹(X_{s̄}, 𝔽_ℓ)| = ℓ^{2 g_s}` and
`|Hʳ(X_{s̄}, 𝔽_ℓ)| = 1` for `r > 2`, and `c` and `g` are constructible functions on `S`: they
take finitely many values, each on a constructible subset. -/
theorem natCard_sheafH_constantZMod_geometricFibre [IsNoetherian S] (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    let Xs : S → Scheme.{u} := fun s ↦ Limits.pullback f (S.geometricPointAt s)
    let c : S → ℕ := fun s ↦ Nat.card (_root_.ConnectedComponents (Xs s))
    let g : S → ℕ := fun s ↦
      letI : (Xs s).Over (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
        ⟨pullback.snd f (S.geometricPointAt s)⟩
      arithmeticGenus (AlgebraicClosure (S.residueField s)) (Xs s)
    (∀ s : S,
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 0) = ℓ ^ c s ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 1) = ℓ ^ (2 * g s) ∧
      Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) 2) = ℓ ^ c s ∧
      ∀ r, 2 < r → Nat.card (Sheaf.H ((Xs s).constantZMod ℓ) r) = 1) ∧
    ((Set.range c).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (c ⁻¹' {m})) ∧
    ((Set.range g).Finite ∧ ∀ m : ℕ, Topology.IsConstructible (g ⁻¹' {m})) := by
  exact natCard_sheafH_constantZMod_geometricFibre_of_smooth f i hi ℓ hℓ

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Constant-coefficient finiteness
for projective smooth curves.

Let `S` be Noetherian, `f : X ⟶ S` projective and smooth of relative dimension one, and `ℓ` a
prime invertible on `S`. Every higher direct image `Rʳf_* 𝔽_ℓ` is constructible. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth [IsNoetherian S]
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (ℓ : ℕ) [Fact ℓ.Prime]
    [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (r : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  subst hi
  have hℓ := isUnit_natCast_of_hasInvertibleExponent_zmod (S := S) ℓ
  have hℓ2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  obtain ⟨hcard, ⟨-, hc⟩, ⟨-, hg⟩⟩ :=
    natCard_sheafH_constantZMod_geometricFibre (i ≫ ℙ(n; S) ↘ S) i rfl ℓ hℓ
  -- the cardinality of `Hʳ` of the geometric fibres, as a function of the point
  have key (r' : ℕ) : (∀ s : S, Nat.card (Sheaf.H ((Limits.pullback (i ≫ ℙ(n; S) ↘ S)
      (S.geometricPointAt s)).constantZMod ℓ) r') ≠ 0) ∧ ∀ m : ℕ,
      Topology.IsConstructible {s : S | Nat.card (Sheaf.H ((Limits.pullback (i ≫ ℙ(n; S) ↘ S)
        (S.geometricPointAt s)).constantZMod ℓ) r') = m} := by
    rcases lt_trichotomy r' 2 with hr | rfl | hr
    · interval_cases r'
      · refine ⟨fun s ↦ by rw [(hcard s).1]; positivity, fun m ↦ ?_⟩
        simp only [fun s ↦ (hcard s).1]
        exact isConstructible_setOf_pow_eq _ hc hℓ2 m
      · refine ⟨fun s ↦ by rw [(hcard s).2.1]; positivity, fun m ↦ ?_⟩
        simp only [fun s ↦ (hcard s).2.1, pow_mul]
        exact isConstructible_setOf_pow_eq _ hg (by nlinarith) m
    · refine ⟨fun s ↦ by rw [(hcard s).2.2.1]; positivity, fun m ↦ ?_⟩
      simp only [fun s ↦ (hcard s).2.2.1]
      exact isConstructible_setOf_pow_eq _ hc hℓ2 m
    · refine ⟨fun s ↦ by simp [(hcard s).2.2.2 r' hr], fun m ↦ ?_⟩
      simp only [fun s ↦ (hcard s).2.2.2 r' hr]
      by_cases hm : 1 = m
      · simp [hm, Topology.IsConstructible.univ]
      · simp [hm, Topology.IsConstructible.empty]
  exact isConstructibleSheaf_homology_rightDerivedLowerStar_of_sheafH_geometricFibre _ ℓ r
    (fun s ↦ Nat.finite_of_card_ne_zero ((key r.toNat).1 s)) fun m _ ↦ (key r.toNat).2 m

variable {k : Type u} [Field k]

/-- The generic step of `proposition-proper-direct-image-finite-coefficients`: over an integral base
`T` of finite type over `k`, the higher direct images of `𝔽_ℓ` along a projective family of
dimension at most one are constructible over a nonempty open `U` of `T`. A generic curve model
(`proposition-proper-direct-image-finite-coefficients`) gives a finite surjection `p : S' ⟶ U` and a
finite comparison `ν : ∐ₐ Yₐ ⟶ T₀` onto the reduction `T₀` of `X_{S'}`, isomorphic off a closed
subscheme finite over `S'`. The direct images from the `Yₐ` are constructible (smooth curves, or
finite morphisms), hence so are those from `T₀`
(`proposition-proper-direct-image-finite-coefficients`) and from `X_{S'}`; they are the pullbacks
along `p` of those over `U` (proper base change), which embed into their finite pushforwards along
`p`. -/
theorem exists_isConstructibleSheaf_homology_rightDerivedLowerStar_zmod_of_isIntegral
    {T : Scheme.{u}} [IsIntegral T] (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT]
    [QuasiCompact aT] (f : X ⟶ T) {n : Type u} [Finite n] (i : X ⟶ ℙ(n; T))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; T) ↘ T = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) T] (q : ℤ) :
    ∃ U : T.Opens, U ≠ ⊥ ∧ IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f ∣_ U)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (f ⁻¹ᵁ U).toScheme.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  have : IsProper f := by
    subst hi
    infer_instance
  obtain ⟨U, hU, S', _, p, _, _, T₀, t, _, _, _, ι, _, Y, ν, _, _, D, d, _, hdfin, hνiso, hY⟩ :=
    exists_isFinite_sigmaDesc_genericCurveModel aT f i hi hf
  refine ⟨U, hU, ?_⟩
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := {}
  let F' := pullback.snd (f ∣_ U) p
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ aT)
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ aT)
  have : IsNoetherian U := {}
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian (p ≫ U.ι ≫ aT)
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (p ≫ U.ι ≫ aT)
  have : IsNoetherian S' := {}
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S' := .of_hom (p ≫ U.ι)
  have : IsProper F' := inferInstance
  -- the direct images from the pieces `Yₐ` of the model are constructible
  have hpieces (a : ι) : Etale.DerivedCategory.constructibleHomology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) S'
      ((R((Sigma.ι Y a ≫ ν ≫ t ≫ F')_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Y a).smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))) := by
    rcases hY a with ⟨⟨m, _, j, _, hj⟩, _⟩ | ⟨_, _⟩
    · exact fun r ↦ isConstructibleSheaf_homology_rightDerivedLowerStar_of_smooth _ j hj ℓ r
    · have : IsConstructibleSheaf ((constantSheaf (Y a).smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) :=
        ⟨Stratification.trivial _, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 _)
          ((constantSheaf (Y a).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))⟩
      exact (boundedConstructible_rightDerivedLowerStar_of_isFinite _ _
        (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)).2
  -- hence those from `∐ₐ Yₐ`
  have hsum : ∀ r : ℤ, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((ν ≫ t ≫ F')_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((ν)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj
            ((constantSheaf T₀.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))) := by
    refine (Etale.DerivedCategory.constructibleHomology _ S').prop_of_iso
      ((R((ν ≫ t ≫ F')_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          ((upperStarConstantSheafIso _ ν).app _).symm))
      (constructibleHomology_rightDerivedLowerStar_sigma Y _ _ fun a ↦ ?_)
    exact (Etale.DerivedCategory.constructibleHomology _ S').prop_of_iso
      ((R((Sigma.ι Y a ≫ ν ≫ t ≫ F')_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          ((upperStarConstantSheafIso _ (Sigma.ι Y a)).app _).symm)) (hpieces a)
  -- the comparison along `ν`, an isomorphism off `D`
  let W : T₀.Opens := ⟨(Set.range d.base)ᶜ, d.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hνW : IsIso (pullback.snd ν W.ι) := by
    have h := (isPullback_morphismRestrict ν W).flip.isoPullback_hom_snd
    have h' : pullback.snd ν W.ι = (isPullback_morphismRestrict ν W).flip.isoPullback.inv ≫
        (ν ∣_ W) := by
      refine (cancel_epi (isPullback_morphismRestrict ν W).flip.isoPullback.hom).1 ?_
      rw [Iso.hom_inv_id_assoc]
      exact h
    rw [h']
    infer_instance
  have hT₀ := (constructible_and_isIso_rightDerivedLowerStarUnitComparison (p ≫ U.ι ≫ aT)
    (t ≫ F') ν d W.ι (by rw [Opens.range_ι]; rfl) hνW
    (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))) hsum).1
  -- from `T₀` to `X_{S'}`, then to `U` by proper base change and finite descent along `p`
  have hP : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((F')_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (pullback (f ∣_ U) p).smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) :=
    IsConstructibleSheaf.of_iso (F := (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((t ≫ F')_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf T₀.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((R((t ≫ F')_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
            ((upperStarConstantSheafIso _ t).app _).symm) ≪≫
        (rightDerivedLowerStarSingleIsoOfSurjective t F' _).symm))
  let E := (_root_.DerivedCategory.homologyFunctor _ q).obj
    ((R((f ∣_ U)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (f ⁻¹ᵁ U).toScheme.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))
  have : IsConstructibleSheaf ((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj E) :=
    IsConstructibleSheaf.of_iso (upperStarHomologyRightDerivedLowerStarConstantSheafIso
      (Λ := ULift.{u + 1} (ZMod ℓ)) (IsPullback.of_hasPullback (f ∣_ U) p)
      (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))) q).symm
  have : IsConstructibleSheaf (((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))] ⋙
      (p)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))]).obj E) :=
    Scheme.IsConstructibleSheaf.lowerStar_of_isFinite p
    ((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj E)
  have := mono_unit_app_of_surjective (ULift.{u + 1} (ZMod ℓ)) p p.surjective E
  exact Scheme.IsConstructibleSheaf.of_mono
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) p).unit.app E)

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Constant coefficients on
projective families of dimension at most one.

Let `f : X ⟶ S` be projective (`f = π ∘ i` for a closed immersion `i : X ⟶ ℙ(n; S)`), with `S`
of finite type over a field `k`, such that every geometric fibre `X ×_S Spec Ω` has dimension at
most one, and let `ℓ` be a prime invertible on `S`. Every higher direct image `Rᵠf_* 𝔽_ℓ` is
constructible. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_zmod (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsProper f := by
    subst hi
    infer_instance
  refine Scheme.isConstructibleSheaf_of_forall_isIntegral _ fun T g _ _ ↦ ?_
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) T := .of_hom g
  -- the base change of `f` to `T` is projective with fibres of dimension at most one
  have hw : pullback.snd f g ≫ g = (pullback.fst f g ≫ i) ≫ ℙ(n; S) ↘ S := by
    rw [Category.assoc, hi, pullback.condition]
  obtain ⟨U, hU, hc⟩ :=
    exists_isConstructibleSheaf_homology_rightDerivedLowerStar_zmod_of_isIntegral
      (g ≫ aS) (pullback.snd f g) (ProjectiveSpace.liftBaseChange _ _ hw)
      (ProjectiveSpace.liftBaseChange_over _ _ hw) (fun Ω _ _ s ↦ by
        rw [IsHomeomorph.topologicalKrullDim_eq _
          (pullbackLeftPullbackSndIso f g s).hom.homeomorph.isHomeomorph]
        exact hf Ω (s ≫ g)) ℓ q
  refine ⟨U, Set.nonempty_iff_ne_empty.2 fun h ↦
    hU (TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_bot.symm)), ?_⟩
  -- `(U ⟶ S)^* Rᵠf_* 𝔽_ℓ` is `Rᵠ` of the restriction to `U` of the base change of `f`
  exact IsConstructibleSheaf.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((R((pullback.snd f g ∣_ U)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          ((upperStarConstantSheafIso _ (pullback.snd f g ⁻¹ᵁ U).ι).app _).symm)) ≪≫
    (upperStarHomologyRightDerivedLowerStarIso
      (isPullback_morphismRestrict (pullback.snd f g) U).flip _ q).symm ≪≫
    (U.ι)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].mapIso
      (upperStarHomologyRightDerivedLowerStarConstantSheafIso (Λ := ULift.{u + 1} (ZMod ℓ))
        (IsPullback.of_hasPullback f g) (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))) q).symm ≪≫
    ((upperStarComp _ U.ι g).app _).symm)

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Finite constant groups on
projective curve families.

Let `f : X ⟶ S` be projective, with `S` of finite type over a field `k`, such that every
geometric fibre has dimension at most one. Let `Λ` be a finite ring whose exponent is invertible
on `S` and `M` a finite `Λ`-module. Every higher direct image `Rᵠf_* M` of the constant sheaf
`M` is constructible.

The blueprint states this for a finite abelian group `M` of order invertible on `S`, i.e. for
`Λ = ℤ/N` with `N = |M|`; the statement for finite modules over a finite ring is what the
constructibility of `Rπ_*` on `ℙ¹_S` (`proposition-proper-direct-image-finite-coefficients`)
consumes. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    [HasInvertibleExponent Λ S] (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  refine isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf_of_zmod Λ f
    (fun ℓ _ _ q ↦ ?_) M q
  exact isConstructibleSheaf_homology_rightDerivedLowerStar_zmod aS f i hi hf ℓ q

end Etale

end AlgebraicGeometry
