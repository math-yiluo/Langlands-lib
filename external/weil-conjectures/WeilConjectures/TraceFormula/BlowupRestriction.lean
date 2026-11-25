/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.EllMonodromyPullback
public import WeilConjectures.TraceFormula.PuncturedRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionCoproduct
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange

/-!
# Restriction through the blow-up of a strictly local surface

This file assembles the proof of the blowup restriction vanishing (blueprint
`lemma-vanishing-restrictions-after-blowing-up--1`). Abstractly: let `T'` be a scheme (in the
application `T - D`), `i' : U' ⟶ T'` an open immersion (`T - (D ∪ H) ⟶ T - D`) and `E` a complex on
`U'` with finite `ℓ`-group monodromy. Suppose given a transverse boundary configuration `(Z, X, Y)`
(in the application, a chart of the blow-up of `T` at `t` minus the strict transform of `D`) and a
morphism `φ : Z - Y ⟶ T'` with `φ⁻¹(U') = Z - (X ∪ Y)` (in the application the blow-up map,
`lemma-vanishing-restrictions-after-blowing-up--1` (2), (3)). Let `ψ : W ⟶ T'` (the punctured curve
`B - t`) be a finite disjoint union of maps `W_j ⟶ Z - Y ⟶ T'` each of which factors through a
strictly local scheme `S_j ⟶ Z` whose closed point lies on `Y` (the strictly local branches of the
strict transform of `B`, `lemma-vanishing-restrictions-after-blowing-up--1`). Then the restriction
map `RΓ(T', i'_! E) ⟶ RΓ(W, ψ^* i'_! E)` is zero: it is the tuple of the restrictions to the `W_j`
(`AlgebraicGeometry.Etale.eq_zero_of_globalSectionsRestriction_of_isColimit`), and each of those
factors through the restriction `RΓ(Z - Y, i_! φ^* E) ⟶ RΓ(W_j, -)`, which vanishes by the
punctured restriction lemma (`lemma-restriction-punctured-curve`,
`AlgebraicGeometry.Etale.globalSectionsRestriction_eq_zero_of_strictlyLocal`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The pullback of a complex with finite `ℓ`-group monodromy has finite `ℓ`-group monodromy. -/
lemma HasFiniteEllMonodromy.upperStar {ℓ : ℕ} {U V : Scheme.{u}} (f : V ⟶ U)
    {E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE : HasFiniteEllMonodromy ℓ E) :
    HasFiniteEllMonodromy ℓ (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) :=
  hE.upperStar' f


variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime] [Finite Λ]
  {Z : Over (Spec (.of k))} {X Y : Scheme.{u}} {iX : X ⟶ Z.left} {iY : Y ⟶ Z.left}
  {UY UXY : Z.left.Opens}

/-- The spectrum of a finite product of rings is the coproduct of the spectra. -/
noncomputable def isColimitCofanSpecPi {J : Type u} [Finite J] (R : J → Type u)
    [∀ j, CommRing (R j)] :
    IsColimit (Cofan.mk (Spec (.of (∀ j, R j)))
      fun j ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom R j))) :=
  have : IsIso (Sigma.desc (Cofan.mk (Spec (.of (∀ j, R j)))
      fun j ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom R j))).inj) :=
    inferInstanceAs (IsIso (sigmaSpec fun j ↦ CommRingCat.of (R j)))
  Cofan.isColimitOfIsIsoSigmaDesc _

/-- **Restriction to a semilocal scheme centred on the boundary vanishes**: the version of
`globalSectionsRestriction_transverseBoundaryComplex_eq_zero` for `S = Spec (∏ R_j)` a finite
disjoint union of strictly local schemes whose closed points map to closed points of `Y`. -/
theorem globalSectionsRestriction_transverseBoundaryComplex_eq_zero_of_pi (hℓ : (ℓ : k) ≠ 0)
    (hΛ : IsNilpotent (ℓ : Λ)) (hZ : IsEtaleLimitOfSmoothSurfaces Z)
    [IsLocallyNoetherian Z.left] [IsRegular Z.left] (hX : IsRegularDivisor iX)
    (hY : IsRegularDivisor iY) (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX))
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    (E : DerivedCategory (Sheaf UXY.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) [ConnectedSpace Y] {J : Type u} [Finite J]
    (R : J → Type u) [∀ j, CommRing (R j)] [∀ j, IsStrictlyHenselianLocalRing (R j)]
    (c : Spec (.of (∀ j, R j)) ⟶ Z.left) (s : J → Y) (hs : ∀ j, IsClosed ({s j} : Set Y))
    (hcs : ∀ j, (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R j)) ≫ c)
      (IsLocalRing.closedPoint (R j)) = iY (s j)) :
    globalSectionsRestriction c (transverseBoundaryComplex hle E) = 0 := by
  refine eq_zero_of_globalSectionsRestriction_of_isColimit _ (isColimitCofanSpecPi R) _ _
    fun j ↦ ?_
  have hc := globalSectionsRestriction_comp c
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R j))) (transverseBoundaryComplex hle E)
  rw [globalSectionsRestriction_transverseBoundaryComplex_eq_zero hℓ hΛ hZ hX hY z hz hXY hUY hUXY
    hle E hE _ (s j) (hs j) (hcs j), zero_comp] at hc
  exact hc.symm

/-- **Restriction through a transverse configuration vanishes** (assembly of the proof of
`lemma-vanishing-restrictions-after-blowing-up--1`). Let `(Z, X, Y, z)` be a transverse boundary
configuration with `Y` connected, `i' : U' ⟶ T'` an open immersion, `E` a complex with finite
`ℓ`-group monodromy on `U'`, and `φ : Z - Y ⟶ T'` with `φ⁻¹(U') = Z - (X ∪ Y)` (a cartesian square).
Let `ψ : W ⟶ T'` factor as `W ⟶ Z - Y ⟶ T'` such that `W ⟶ Z - Y ⟶ Z` factors through a finite
disjoint union `S = Spec (∏ R_j) ⟶ Z` of strictly local schemes mapping their closed points to
closed points of `Y`. Then the restriction map `RΓ(T', i'_! E) ⟶ RΓ(W, ψ^* i'_! E)` is zero. -/
theorem globalSectionsRestriction_eq_zero_of_transverse (hℓ : (ℓ : k) ≠ 0)
    (hΛ : IsNilpotent (ℓ : Λ)) (hZ : IsEtaleLimitOfSmoothSurfaces Z)
    [IsLocallyNoetherian Z.left] [IsRegular Z.left] (hX : IsRegularDivisor iX)
    (hY : IsRegularDivisor iY) (z : Z.left) (hz : MeetTransverselyAt iX iY z)
    (hXY : IsRegularImmersion 2 (pullback.fst iX iY ≫ iX))
    (hUY : (UY : Set Z.left) = (Set.range iY)ᶜ)
    (hUXY : (UXY : Set Z.left) = (Set.range iX ∪ Set.range iY)ᶜ) (hle : UXY ≤ UY)
    [ConnectedSpace Y] {T' U' : Scheme.{u}} (i' : U' ⟶ T') [IsOpenImmersion i']
    (E : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : HasFiniteEllMonodromy ℓ E) (φ : UY.toScheme ⟶ T') (φU : UXY.toScheme ⟶ U')
    (hφ : IsPullback φU (Z.left.homOfLE hle) i' φ) {W : Scheme.{u}} (ψ : W ⟶ T')
    {J : Type u} [Finite J] (R : J → Type u) [∀ j, CommRing (R j)]
    [∀ j, IsStrictlyHenselianLocalRing (R j)] (c : Spec (.of (∀ j, R j)) ⟶ Z.left) (s : J → Y)
    (hs : ∀ j, IsClosed ({s j} : Set Y))
    (hcs : ∀ j, (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R j)) ≫ c)
      (IsLocalRing.closedPoint (R j)) = iY (s j))
    (ι : W ⟶ UY.toScheme) (jW : W ⟶ Spec (.of (∀ j, R j))) (hι : ι ≫ UY.ι = jW ≫ c)
    (hψ : ψ = ι ≫ φ) :
    globalSectionsRestriction ψ (((i')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E) =
      0 := by
  let F := ((i')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E
  let EZ := ((φU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj E
  have hZero : globalSectionsRestriction ι
      (((Z.left.homOfLE hle)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj EZ) = 0 :=
    globalSectionsRestriction_eq_zero_of_factor UY.ι c _
      (globalSectionsRestriction_transverseBoundaryComplex_eq_zero_of_pi hℓ hΛ hZ hX hY z hz hXY hUY
        hUXY hle EZ (hE.upperStar φU) R c s hs hcs) ι jW hι
  have hφι : globalSectionsRestriction ι
      (((φ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj F) = 0 := by
    let e : ((φ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj F ≅
        ((Z.left.homOfLE hle)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj EZ :=
      ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) hφ).app E).symm
    have hn := globalSectionsRestriction_naturality ι e.hom
    rw [hZero, comp_zero] at hn
    have hid : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).map
        (((ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map e.hom) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).map
          (((ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map e.inv) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id]
    rw [← Category.comp_id (globalSectionsRestriction ι _), ← hid, ← Category.assoc, ← hn,
      zero_comp]
  rw [hψ]
  exact globalSectionsRestriction_comp_eq_zero_of_right _ _ _ hφι

end AlgebraicGeometry.Etale
