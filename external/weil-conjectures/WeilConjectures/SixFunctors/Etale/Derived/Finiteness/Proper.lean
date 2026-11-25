/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma.ProjectiveModification
public import WeilConjectures.AlgebraicGeometry.GeometricFibreDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective

/-!
# Constructibility of proper direct images

Let `k` be a field and `Λ` a finite ring killed by an integer invertible in `k`. For a proper
morphism `f : X ⟶ S` with `S` of finite type over `k`:

- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper`
  (`proposition-proper-direct-image-finite-coefficients`): `𝒞(f)` holds. The proof is Noetherian
  induction on closed subsets of `X`, using a projective modification given by Chow's lemma
  (`AlgebraicGeometry.exists_projective_modification`), the projective case and the transfer
  along modifications `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_modification`.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper`
  (`proposition-proper-direct-image-finite-coefficients`): moreover `Rᵠf_* F = 0` for `q > 2d` if
  the geometric fibres have dimension at most `d`. The vanishing is checked at geometric points, by
  proper base change (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`) and
  the cohomological dimension of the geometric fibres.
- `AlgebraicGeometry.Etale.isIso_homology_derivedBaseChangeMapPlus_of_isProper`
  (`obl-fin-comparison`): the comparison with the cohomology of geometric fibres.
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`
  (`theorem-results-from-etale-theory--3`): `Rf_*` preserves `D^b_c`. The blueprint uses the
  hypercohomology spectral sequence; we use the dévissage along truncation triangles
  `AlgebraicGeometry.Etale.boundedConstructible_obj_of_forall_singleFunctor`, the fibre
  dimensions being uniformly bounded by `AlgebraicGeometry.exists_topologicalKrullDim_pullback_le`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Proper direct-image
constructibility.

Let `Λ` be a finite ring killed by an integer invertible in the field `k`. Every proper morphism
`f : X ⟶ S` with `S` of finite type over `k` satisfies `𝒞(f)`: the higher direct images
`Rᵠf_* F` of constructible sheaves `F` of `Λ`-modules are constructible. -/
theorem hasConstructibleDirectImages_of_isProper {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f] :
    HasConstructibleDirectImages Λ f := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ aS)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ aS)
  have : IsNoetherian X := {}
  -- Noetherian induction on the closed subsets `C` of `X`
  suffices H : ∀ C : TopologicalSpace.Closeds X, ∀ (Z : Scheme.{u}) (i : Z ⟶ X)
      [IsClosedImmersion i], Set.range i.base = C → HasConstructibleDirectImages Λ (i ≫ f) by
    simpa using H ⊤ X (𝟙 X) (by simp)
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
  intro Z i _ hi
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f ≫ aS)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (i ≫ f ≫ aS)
  obtain ⟨Y, π, U, _, _, hU, hπU, N, _, e, _, he⟩ := exists_projective_modification (i ≫ f)
  have hY : HasConstructibleDirectImages Λ (π ≫ i ≫ f) :=
    hasConstructibleDirectImages_of_isClosedImmersion aS _ N e he
  by_cases hZ : IsEmpty Z
  · exact HasConstructibleDirectImages.of_comp_of_isFinite (i ≫ f ≫ aS) _ π hY
  rw [not_isEmpty_iff] at hZ
  have hπ : IsIso (pullback.snd π U.ι) := by
    have : IsIso ((pullbackRestrictIsoRestrict π U).inv ≫ pullback.snd π U.ι) := hπU
    exact IsIso.of_isIso_comp_left (pullbackRestrictIsoRestrict π U).inv _
  refine HasConstructibleDirectImages.of_modification (i ≫ f) π U.ι U.closedComplement
    (by simp) hπ hY ?_
  -- the closed complement of `U` has strictly smaller image in `X`
  let C' : TopologicalSpace.Closeds X :=
    ⟨Set.range (U.closedComplement ≫ i).base,
      (U.closedComplement ≫ i).isClosedEmbedding.isClosed_range⟩
  have hlt : C' < C := by
    refine lt_of_le_of_ne ?_ fun h ↦ ?_
    · rintro _ ⟨z, rfl⟩
      rw [← SetLike.mem_coe, ← hi]
      exact ⟨_, rfl⟩
    · obtain ⟨z, hz⟩ := hU.nonempty
      have : i.base z ∈ (C' : Set X) := by rw [h, ← hi]; exact ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := this
      have hw' : U.closedComplement.base w = z :=
        i.isClosedEmbedding.injective (by simpa using hw)
      have : U.closedComplement.base w ∈ Set.range U.closedComplement.base := ⟨w, rfl⟩
      rw [Scheme.Opens.range_closedComplement, hw'] at this
      exact this hz
  simpa using ih C' hlt _ (U.closedComplement ≫ i) rfl

/-- The cohomology of the geometric fibre of a proper morphism vanishes above twice the
dimension of the fibre: for `f : X ⟶ S` proper, a point `s : Spec Ω ⟶ S` with `Ω` separably
closed whose fibre `X_s` has dimension at most `d`, and a sheaf `F` of `Λ`-modules on `X`,
`Hᵠ(X_s, F|_{X_s}) = 0` for `q > 2d`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`, blueprint
`proposition-proper-direct-image-finite-coefficients`). -/
lemma isZero_homology_fibre_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (d : ℕ)
    (hd : topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero ((Plus.homologyFunctor _ q).obj
      ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        (((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
          ((Plus.singleFunctor _ 0).obj F)))) := by
  have : IsProper (pullback.snd f s) := MorphismProperty.pullback_snd _ _ inferInstance
  exact (Etale.isZero_higherDirectImage_of_two_mul_lt isAddTorsion_of_finite (pullback.snd f s)
    (pullback.snd f s) (𝟙 _) (Category.comp_id _) d hd
    ((pullback.fst f s)^*[ModuleCat.{u + 1} Λ].obj F) q hq).of_iso
      ((Plus.homologyFunctor _ q).mapIso
        ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
          ((((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
            0).app F)))

/-- The homology sheaves of the unbounded derived direct image `Rf_*(F[0])` are those of the
bounded below derived direct image `R⁺f_*(F[0])`. -/
noncomputable def homologyRightDerivedLowerStarSingleIsoPlus {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)) ≅
      (Plus.homologyFunctor _ q).obj ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        ((Plus.singleFunctor _ 0).obj F)) :=
  (homologyFunctor _ q).mapIso
    (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
      ((Plus.singleFunctor _ 0).obj F)).symm

/-- **Vanishing of proper direct images above twice the fibre dimension.** For `f : X ⟶ S`
proper all of whose geometric fibres have dimension at most `d`, `Rᵠf_* F = 0` for `q > 2d` and
every sheaf `F` of `Λ`-modules: at a geometric point `s`, proper base change identifies
`s^* Rᵠf_* F` with `Hᵠ(X_s, F|_{X_s})`
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`), which vanishes by
`AlgebraicGeometry.Etale.isZero_homology_fibre_of_isProper`, and geometric points detect zero
sheaves. -/
lemma isZero_homology_rightDerivedLowerStar_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) := by
  refine IsZero.of_iso ?_ (homologyRightDerivedLowerStarSingleIsoPlus f F q)
  refine Etale.isZero_of_forall_isZero_upperStar_algClosurePoint Λ _ fun t ↦ ?_
  let x := S.algClosurePoint t
  let sq := IsPullback.of_hasPullback f x
  let K := (Plus.singleFunctor _ 0).obj F
  have := Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq K
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X isAddTorsion_of_finite K)
  exact (isZero_homology_fibre_of_isProper f x d (hd _ x) F q hq).of_iso
    (((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapDerivedCategoryPlusHomologyFunctorIso q).app
        ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K) ≪≫
      (Plus.homologyFunctor _ q).mapIso
        (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)))

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: The proper case: direct images
of proper morphisms.

Let `f : X ⟶ S` be a proper morphism with `S` of finite type over `k`, all of whose geometric
fibres have dimension at most `d`, and let `F` be a constructible sheaf of `Λ`-modules on `X_ét`,
`Λ` a finite ring killed by an integer invertible in `k`. Then `Rᵠf_* F` is constructible on
`S_ét` for every `q`, and `Rᵠf_* F = 0` for `q > 2d`. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f]
    (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)))) ∧
    ∀ q : ℤ, (2 * d : ℤ) < q → IsZero ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) :=
  ⟨fun q ↦ hasConstructibleDirectImages_of_isProper aS f F inferInstance q,
    isZero_homology_rightDerivedLowerStar_of_isProper f d hd F⟩


/-- Blueprint `obl-fin-comparison`: The comparison and finitude of proper direct images.

Let `f : X ⟶ S` be a proper morphism with `S` of finite type over `k`, whose geometric fibres
have dimension at most `d`, and let `F` be a constructible sheaf of `Λ`-modules on `X_ét`, for a
finite ring `Λ` killed by an integer invertible in `k`. Let `s : Spec Ω ⟶ S` be a geometric point
(`Ω` algebraically closed), with geometric fibre `X_s = X ×_S Spec Ω`, projections
`i_s : X_s ⟶ X` and `a_s : X_s ⟶ Spec Ω`. Then:

1. (the comparison) for every `q`, the base change map `s^*(Rᵠf_* F) ⟶ Hᵠ(X_s, F|_{X_s})`
   (the `q`-th homology of `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` at `F`, the
   right-hand side being the sheaf `Rᵠa_{s*}(i_s^* F)` on `Spec Ω`) is an isomorphism, the
   fibre cohomology is finite, and it vanishes for `q > 2d`;
2. (the finitude) every `Rᵠf_* F` is constructible, and `Rᵠf_* F = 0` for `q > 2d`. -/
theorem isIso_homology_derivedBaseChangeMapPlus_of_isProper {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f]
    (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (q : ℤ),
      IsIso ((Plus.homologyFunctor _ q).map ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f s).toCommSq).app ((Plus.singleFunctor _ 0).obj F))) ∧
      IsFiniteSheaf ((Plus.homologyFunctor _ q).obj
        ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
          (((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
            ((Plus.singleFunctor _ 0).obj F)))) ∧
      ((2 * d : ℤ) < q → IsZero ((Plus.homologyFunctor _ q).obj
        ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
          (((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
            ((Plus.singleFunctor _ 0).obj F)))))) ∧
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)))) ∧
    ∀ q : ℤ, (2 * d : ℤ) < q → IsZero ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) := by
  obtain ⟨h₁, h₂⟩ := isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper aS f d hd F
  refine ⟨fun Ω _ _ s q ↦ ?_, h₁, h₂⟩
  let sq := IsPullback.of_hasPullback f s
  let K := (Plus.singleFunctor _ 0).obj F
  have := Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq K
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X isAddTorsion_of_finite K)
  refine ⟨inferInstance, ?_, isZero_homology_fibre_of_isProper f s d (hd Ω s) F q⟩
  have : IsFiniteSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) :=
    (h₁ q).isFiniteSheaf
  have := IsFiniteSheaf.upperStar s ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)))
  exact IsFiniteSheaf.of_iso ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).mapIso
      (homologyRightDerivedLowerStarSingleIsoPlus f F q) ≪≫
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlusHomologyFunctorIso q).app
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K) ≪≫
    (Plus.homologyFunctor _ q).mapIso
      (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)))


/-- Blueprint `theorem-results-from-etale-theory--3`: Bounded constructible complexes under a
proper direct image.

Let `b : Y ⟶ S` be proper with `S` of finite type over `k`, and let `Λ` be a finite ring killed
by an integer invertible in `k`. For `K ∈ D^b_c(Y, Λ)`, the derived direct image `Rb_* K` lies in
`D^b_c(S, Λ)`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper {Y S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (b : Y ⟶ S) [IsProper b]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_pullback_le aS b
  refine boundedConstructible_obj_of_forall_singleFunctor Λ _ (fun F hF ↦ ?_) hK
  obtain ⟨h₁, h₂⟩ := isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper aS b d
    (fun Ω _ _ s ↦ hd Ω s) F
  exact ⟨⟨⟨0, ((b)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj_singleFunctor F⟩,
    ⟨2 * d, (isLE_iff _ _).2 fun q hq ↦ h₂ q hq⟩⟩, h₁⟩


end Etale

end AlgebraicGeometry
