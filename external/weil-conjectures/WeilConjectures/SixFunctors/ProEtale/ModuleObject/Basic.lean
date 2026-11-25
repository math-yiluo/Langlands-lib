/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstantPushout
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent

/-!

# Condensed coefficient rings and their canonical coefficient morphisms

Let `Λ` be a condensed ring, i.e. a ring object of abelian sheaves on the pro-étale site of a
point `*_proét = (Profinite, coherent topology)`, for instance the condensed rings
`T̲ = C(-, T)` of `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`. Following
Sections 4 and 5 of `WeilConjectures/RefactorInstruction.tex`, this file pulls `Λ` back to every
scheme `X`,
```
Λ_X := p_X^* Λ,
```
along the canonical morphism `p_X : X_proét ⟶ *_proét`, and constructs explicitly the
isomorphisms of ring objects
```
α_f : f^* Λ_Y ≅ Λ_X
```
for every morphism of schemes `f : X ⟶ Y`. These are the coefficient rings and the canonical
coefficient morphisms of the six functors on module objects over `Λ_X`, built in the other files
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject`.

## The profinite test objects

For a profinite set `S`, the ring `LC(S, ℤ)` of locally constant functions `S → ℤ` is the
filtered colimit of the finite products `ℤ^{S_i}` over the finite quotients `S_i` of `S`, so
```
Spec LC(S, ℤ) = lim_i ∐_{S_i} Spec ℤ,
```
the profinite set `S` regarded as a pro-étale scheme over `Spec ℤ`
(`AlgebraicGeometry.ProEtale.profiniteToProEt`). For a scheme `X` with structure morphism
`π_X : X ⟶ Spec ℤ`, the base change
```
X[S] := Spec LC(S, ℤ) ×_{Spec ℤ} X = lim_i ∐_{S_i} X
```
is the pro-étale `X`-scheme of the notes (`AlgebraicGeometry.ProEtale.profiniteToProEtOf`). The
functor `S ↦ X[S]` is the composite of `S ↦ Spec LC(S, ℤ)` with the base change along `π_X`.

## The morphism `p_X` and the comparison `α_f`

Accordingly, the inverse image along `p_X` is the composite
```
p_X^* := π_X^* ∘ p^*,
```
where `p^* : Sheaf *_proét Ab ⥤ Sheaf (Spec ℤ)_proét Ab` is the inverse image along the
continuous functor `S ↦ Spec LC(S, ℤ)` (`AlgebraicGeometry.ProEtale.pointUpperStar`). It is
strong monoidal and braided, so for a commutative condensed ring `Λ` the pullback
`Λ_X = p_X^* Λ` is a commutative ring object of abelian sheaves on `X_proét`
(`AlgebraicGeometry.ProEtale.condensedRingObj`). For `f : X ⟶ Y`, the structure morphisms
satisfy `f ≫ π_Y = π_X`, `Spec ℤ` being terminal, and the comparison
```
f^* p_Y^* = f^* π_Y^* p^* ≅ (f ≫ π_Y)^* p^* = π_X^* p^* = p_X^*
```
is the composition isomorphism `ProEtale.upperStarComp` of the pullbacks, which on the test
objects is the canonical isomorphism `X ×_Y Y[S] ≅ X[S]` of the notes
(`AlgebraicGeometry.ProEtale.upperStarFromPointComp`).

## The canonical coefficient morphisms

* `α_f : f^* Λ_Y ⟶ Λ_X` (`AlgebraicGeometry.ProEtale.condensedPullbackHom`): the component at
  `Λ` of the comparison `f^* ∘ p_Y^* ≅ p_X^*`. It is a morphism of ring objects, and an
  isomorphism for *every* `f`: the coefficients pulled back from the point form a
  Cartesian system. As a morphism of bundled ring objects it is
  `AlgebraicGeometry.ProEtale.coefficientPullbackIso`.
* `η_f : Λ_Y ⟶ f_* Λ_X` (`AlgebraicGeometry.ProEtale.condensedPushforwardHom`): the mate of
  `α_f` under the adjunction `f^* ⊣ f_*`, i.e. the unit `Λ_Y ⟶ f_* f^* Λ_Y` followed by `f_* α_f`.

This file also records the instance `AddCommGrpCat.hasFunctorialFlatResolution`, which the
derived functors on module objects need.

## Main definitions

* `AlgebraicGeometry.ProEtale.profiniteToProEt`: the functor `S ↦ Spec LC(S, ℤ)` from
  profinite sets to the pro-étale site of `Spec ℤ`.
* `AlgebraicGeometry.ProEtale.pointUpperStar`: the inverse image `p^*` from condensed abelian
  groups to abelian sheaves on `(Spec ℤ)_proét`.
* `AlgebraicGeometry.ProEtale.upperStarFromPoint`: the inverse image `p_X^* = π_X^* ∘ p^*`.
* `AlgebraicGeometry.ProEtale.condensedRingObj`: the ring object `Λ_X = p_X^* Λ`, and
  `AlgebraicGeometry.ProEtale.coefficientRing`: the same as a bundled ring object.
* `AlgebraicGeometry.ProEtale.upperStarFromPointComp`: the natural isomorphism
  `f^* ∘ p_Y^* ≅ p_X^*`.
* `AlgebraicGeometry.ProEtale.condensedPullbackHom` and
  `AlgebraicGeometry.ProEtale.condensedPushforwardHom`: the coefficient morphisms `α_f` and `η_f`.

## Main results

* `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`: `Spec LC(S, ℤ) ⟶ Spec ℤ`
  is weakly étale, `LC(S, ℤ)` being weakly étale over `ℤ` (`LocallyConstant.weaklyEtale`).
* `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt`: the functor
  `S ↦ Spec LC(S, ℤ)` preserves finite limits: `LC(-, ℤ)` sends a fibre product of profinite
  sets to a pushout of rings (`Profinite.isPushout_locallyConstant_pullback`), and the point
  to `ℤ`.
* `AlgebraicGeometry.ProEtale.coverPreserving_profiniteToProEt`: it sends a finite jointly
  surjective family to a pro-étale covering, the underlying space of `Spec LC(S, ℤ)` being
  `S × Spec ℤ` (`LocallyConstant.homeomorphPrimeSpectrum`). This is Lemma 4.2 of the notes.
* `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar` and
  `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`: `p^*` is strong monoidal, being the
  sheafification of a left Kan extension along a representably flat functor.
* `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`: the comparison
  `f^* ∘ p_Y^* ≅ p_X^*` is a monoidal natural isomorphism. It is built from the conjugate of
  the composition isomorphism of pushforwards, which is monoidal by
  `ProEtale.isMonoidal_lowerStarComp`.
* `AlgebraicGeometry.ProEtale.condensedPushforwardHom_id` and
  `AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp`: `η` is compatible with the identity
  and composition isomorphisms of the pushforwards. These are the cases `F = p^* Λ` of the general
  coherences `ProEtale.unitCompUpperStarComp_id` and `ProEtale.unitCompUpperStarComp_comp` of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

/-- Abelian groups admit functorial flat resolutions: the unit `ℤ` of the tensor product is a
flat separator of `Ab`, so `∐_{ℤ ⟶ M} ℤ`, the free abelian group on `M`, is flat and surjects
functorially onto `M`. This is the instance of `WeilConjectures.CategoryTheory.RingObjects.Ab`.
-/
instance AddCommGrpCat.hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution Ab.{u} := by
  infer_instance

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### `Spec ℤ` and the structure morphisms -/

/-- The terminal scheme `Spec ℤ`, in the universe `u`. -/
noncomputable abbrev specZ : Scheme.{u} :=
  Spec (.of (ULift.{u} ℤ))

/-- The structure morphism `π_X : X ⟶ Spec ℤ`. -/
noncomputable abbrev toSpecZ (X : Scheme.{u}) : X ⟶ specZ :=
  specULiftZIsTerminal.from X

/-- The structure morphisms are compatible with every morphism of schemes, `Spec ℤ` being
terminal. -/
lemma comp_toSpecZ {X Y : Scheme.{u}} (f : X ⟶ Y) : f ≫ toSpecZ Y = toSpecZ X :=
  specULiftZIsTerminal.hom_ext _ _

/-! ### Profinite sets as pro-étale schemes over `Spec ℤ` -/

/-- The functor `S ↦ LC(S, ℤ)` sending a profinite set to its ring of locally constant
integer-valued functions, contravariantly by precomposition. -/
noncomputable def profiniteToCommRingCatOp : Profinite.{u} ⥤ CommRingCat.{u}ᵒᵖ where
  obj S := op (CommRingCat.of (LocallyConstant S ℤ))
  map f := (CommRingCat.ofHom (LocallyConstant.comapRingHom f.hom.hom)).op

/-- The functor `S ↦ Spec LC(S, ℤ) = lim_i ∐_{S_i} Spec ℤ`, the profinite set `S` regarded as a
scheme. -/
noncomputable def profiniteToScheme : Profinite.{u} ⥤ Scheme.{u} :=
  profiniteToCommRingCatOp ⋙ Scheme.Spec

/-- `Spec LC(S, ℤ) ⟶ Spec ℤ` is weakly étale. See the module docstring. -/
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S)) := by
  let e : CommRingCat.of (LocallyConstant S (ULift.{u} ℤ)) ≅
      CommRingCat.of (LocallyConstant S ℤ) :=
    (LocallyConstant.congrRightRingEquiv ULift.ringEquiv).toCommRingCatIso
  have : WeaklyEtale
      (Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (LocallyConstant S (ULift.{u} ℤ))))) := by
    infer_instance
  rwa [specULiftZIsTerminal.hom_ext
    (Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (LocallyConstant S (ULift.{u} ℤ)))))
    (toSpecZ (profiniteToScheme.obj S))] at this

/-- The functor `S ↦ Spec LC(S, ℤ)` from profinite sets to the pro-étale site of `Spec ℤ`. -/
noncomputable def profiniteToProEt : Profinite.{u} ⥤ specZ.{u}.ProEt where
  obj S := ProEt.mk (toSpecZ (profiniteToScheme.obj S))
  map f := MorphismProperty.Over.homMk (profiniteToScheme.map f) (comp_toSpecZ _)
  map_id S := MorphismProperty.Over.Hom.ext (profiniteToScheme.map_id S)
  map_comp f g := MorphismProperty.Over.Hom.ext (profiniteToScheme.map_comp f g)

lemma profiniteToProEt_obj_left (S : Profinite.{u}) :
    (profiniteToProEt.obj S).left = Spec (.of (LocallyConstant S ℤ)) :=
  rfl

-- Ring maps from locally constant integer-valued functions are determined by their
-- map on profinite components. Characteristic functions identify their values after
-- localization; conversely, `liftPrimeSpectrum` glues integers along clopen partitions.
-- This constructs a left adjoint to `profiniteToCommRingCatOp`, avoiding tensor-product
-- and equalizer computations. Source: the module's profinite-test-object construction
-- and `LocallyConstant.homeomorphPrimeSpectrum` / `LocallyConstant.liftPrimeSpectrum`.
private noncomputable def profiniteSpectrumProjection {S : Profinite.{u}} {R : Type u} [CommRing R]
    (φ : LocallyConstant S ℤ →+* R) : C(PrimeSpectrum R, S) :=
  ⟨fun p ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (PrimeSpectrum.comap φ p)).1,
    continuous_fst.comp
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous.comp
        (PrimeSpectrum.continuous_comap φ))⟩

private lemma profinite_localization_map_eq_eval {S : Profinite.{u}} {R : Type u} [CommRing R]
    (φ : LocallyConstant S ℤ →+* R) (p : PrimeSpectrum R) (g : LocallyConstant S ℤ) :
    algebraMap R (Localization.AtPrime p.asIdeal) (φ g) =
      algebraMap R (Localization.AtPrime p.asIdeal) (g (profiniteSpectrumProjection φ p) : R) := by
  classical
  let s := profiniteSpectrumProjection φ p
  let q := ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    (PrimeSpectrum.comap φ p)).2
  have hp : PrimeSpectrum.comap φ p = LocallyConstant.toPrimeSpectrum (s, q) :=
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).apply_symm_apply _).symm
  let χ := LocallyConstant.charFn ℤ (g.isLocallyConstant.isClopen_fiber (g s))
  have hχ : φ χ ∉ p.asIdeal := by
    change χ ∉ (PrimeSpectrum.comap φ p).asIdeal
    rw [hp, LocallyConstant.mem_toPrimeSpectrum_asIdeal]
    simpa [χ, LocallyConstant.charFn_apply_of_mem] using q.isPrime.one_notMem
  have hid : IsIdempotentElem χ := by
    change χ * χ = χ
    ext x
    by_cases hx : g x = g s
    · simp [χ, LocallyConstant.charFn_apply_of_mem, hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have hχloc : algebraMap R (Localization.AtPrime p.asIdeal) (φ χ) = 1 :=
    (hid.map φ).algebraMap_localization_atPrime_of_notMem hχ
  have hmul : χ * g = χ * (g s : LocallyConstant S ℤ) := by
    ext x
    change χ x * g x = χ x * g s
    by_cases hx : g x = g s
    · simp [hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have h := congrArg (fun v ↦ algebraMap R (Localization.AtPrime p.asIdeal) (φ v)) hmul
  simpa only [map_mul, map_intCast, hχloc, one_mul] using h

private noncomputable def profiniteLocallyConstantHomEquiv
    (R : CommRingCat.{u}ᵒᵖ) (S : Profinite.{u}) :
    (Profinite.of (ConnectedComponents (PrimeSpectrum R.unop)) ⟶ S) ≃
      (R ⟶ profiniteToCommRingCatOp.obj S) where
  toFun f := (CommRingCat.ofHom (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R.unop)
    ⟨fun p ↦ f (ConnectedComponents.mk p), f.hom.hom.continuous.comp
      ConnectedComponents.continuous_coe⟩)).op
  invFun φ := ConcreteCategory.ofHom
    ⟨(profiniteSpectrumProjection φ.unop.hom).continuous.connectedComponentsLift,
      (profiniteSpectrumProjection φ.unop.hom).continuous.connectedComponentsLift_continuous⟩
  left_inv f := by
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe x
    change (profiniteSpectrumProjection (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R.unop)
      ⟨fun p ↦ f (ConnectedComponents.mk p), f.hom.hom.continuous.comp
        ConnectedComponents.continuous_coe⟩)) p = f (ConnectedComponents.mk p)
    dsimp [profiniteSpectrumProjection]
    rw [LocallyConstant.comap_liftPrimeSpectrum]
    exact congrArg Prod.fst
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm_apply_apply _)
  right_inv φ := by
    apply Quiver.Hom.unop_inj
    ext g
    apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
    intro p
    change algebraMap R.unop (Localization.AtPrime p.asIdeal)
        (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R.unop)
          (profiniteSpectrumProjection φ.unop.hom) g) = _
    rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
    exact (profinite_localization_map_eq_eval φ.unop.hom p g).symm

private lemma profiniteLocallyConstantHomEquiv_naturality (R : CommRingCat.{u}ᵒᵖ)
    (S T : Profinite.{u}) (g : S ⟶ T)
    (f : Profinite.of (ConnectedComponents (PrimeSpectrum R.unop)) ⟶ S) :
    profiniteLocallyConstantHomEquiv R T (f ≫ g) =
      profiniteLocallyConstantHomEquiv R S f ≫ profiniteToCommRingCatOp.map g := by
  apply Quiver.Hom.unop_inj
  ext h
  apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
  intro p
  change algebraMap R.unop (Localization.AtPrime p.asIdeal)
      (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R.unop) _ h) =
    algebraMap R.unop (Localization.AtPrime p.asIdeal)
      (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R.unop) _
        (LocallyConstant.comapRingHom g.hom.hom h))
  rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum,
    LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
  rfl

/-- The functor `S ↦ Spec LC(S, ℤ)` preserves finite limits. See the module docstring. -/
instance preservesFiniteLimits_profiniteToProEt : PreservesFiniteLimits profiniteToProEt.{u} := by
  have h := (Adjunction.adjunctionOfEquivLeft profiniteLocallyConstantHomEquiv
    profiniteLocallyConstantHomEquiv_naturality).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits profiniteToCommRingCatOp.{u} := inferInstance
  have : PreservesFiniteLimits profiniteToScheme.{u} := by
    unfold profiniteToScheme
    infer_instance
  have : (Over.forget specZ.{u}).IsEquivalence :=
    (Over.equivalenceOfIsTerminal specULiftZIsTerminal).isEquivalence_functor
  have : PreservesFiniteLimits
      ((profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) ⋙ Over.forget specZ) :=
    inferInstanceAs (PreservesFiniteLimits profiniteToScheme.{u})
  have : PreservesFiniteLimits (profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Over.forget specZ)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.ProEt.forget specZ)

instance : RepresentablyFlat profiniteToProEt.{u} :=
  flat_of_preservesFiniteLimits _

/-- The functor `S ↦ Spec LC(S, ℤ)` sends finite jointly surjective families to pro-étale
coverings. See the module docstring. -/
lemma coverPreserving_profiniteToProEt :
    CoverPreserving (coherentTopology Profinite.{u}) (ProEt.topology specZ) profiniteToProEt := by
  classical
  constructor
  intro T R hR
  obtain ⟨ι, hι, S, f, hf, hRf⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mp hR
  have hsurj := ((Profinite.effectiveEpiFamily_tfae S f).out 1 3).mp hf
  have hgeom : ∀ q : profiniteToScheme.obj T,
      ∃ i, q ∈ Set.range (profiniteToScheme.map (f i)) := by
    intro q
    obtain ⟨⟨t, p⟩, rfl⟩ := LocallyConstant.toPrimeSpectrum_surjective q
    obtain ⟨i, s, hs⟩ := hsurj t
    refine ⟨i, LocallyConstant.toPrimeSpectrum (s, p), ?_⟩
    subst t
    rfl
  have hwe (i : ι) : WeaklyEtale (profiniteToScheme.map (f i)) := by
    have : WeaklyEtale (profiniteToScheme.map (f i) ≫
        toSpecZ (profiniteToScheme.obj T)) := by
      rw [comp_toSpecZ]
      infer_instance
    exact WeaklyEtale.of_comp _ (toSpecZ (profiniteToScheme.obj T))
  let C := Scheme.Cover.mkOfCovers (P := @WeaklyEtale) ι
    (fun i ↦ profiniteToScheme.obj (S i)) (fun i ↦ profiniteToScheme.map (f i))
    hgeom hwe
  have (i : C.I₀) : QuasiCompact (C.f i) := by
    change QuasiCompact (Spec.map _)
    infer_instance
  have : Finite C.I₀ := hι
  have hcov : Presieve.ofArrows (fun i ↦ profiniteToProEt.obj (S i))
      (fun i ↦ profiniteToProEt.map (f i)) ∈ ProEt.precoverage specZ (profiniteToProEt.obj T) := by
    rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact (Scheme.Cover.ofQuasiCompactCover C).mem₀
  apply (ProEt.topology specZ).superset_covering _
    (Precoverage.generate_mem_toGrothendieck hcov)
  rw [Sieve.generate_le_iff]
  intro W g hg
  obtain ⟨i⟩ := hg
  exact R.image_mem_functorPushforward profiniteToProEt (hRf i)

instance isContinuous_profiniteToProEt :
    profiniteToProEt.IsContinuous (coherentTopology Profinite.{u}) (ProEt.topology specZ) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    coverPreserving_profiniteToProEt

/-- The left Kan extensions along the opposite of `S ↦ Spec LC(S, ℤ)` exist: the indexing comma
categories are essentially small in `u + 1` and `Ab.{u + 1}` has colimits of that size
(`Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize`). -/
instance hasLeftKanExtension_op_profiniteToProEt (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
    profiniteToProEt.op.HasLeftKanExtension F := by
  infer_instance

/-- The profinite test object `X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X = lim_i ∐_{S_i} X` over a
scheme `X`, as a functor from profinite sets to the pro-étale site of `X`. -/
noncomputable def profiniteToProEtOf (X : Scheme.{u}) : Profinite.{u} ⥤ X.ProEt :=
  profiniteToProEt ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)

/-! ### The inverse image `p^*` from the point -/

/-- The direct image `p_*` from abelian sheaves on `(Spec ℤ)_proét` to condensed abelian
groups, `(p_* G)(S) = G(Spec LC(S, ℤ))`. -/
noncomputable def pointLowerStar :
    Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  profiniteToProEt.sheafPushforwardContinuous Ab.{u + 1} (coherentTopology Profinite.{u})
    (ProEt.topology specZ)

/-- The inverse image `p^*` from condensed abelian groups to abelian sheaves on
`(Spec ℤ)_proét`: left Kan extension along `S ↦ Spec LC(S, ℤ)` followed by sheafification. -/
noncomputable def pointUpperStar :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt Ab.{u + 1}
    (coherentTopology Profinite.{u}) (ProEt.topology specZ)

/-- The adjunction `p^* ⊣ p_*`. -/
noncomputable def pointUpperStarLowerStarAdjunction : pointUpperStar.{u} ⊣ pointLowerStar :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt Ab.{u + 1}
    (coherentTopology Profinite.{u}) (ProEt.topology specZ)

/-- The direct image `p_*` is lax monoidal, being the pushforward along a continuous functor. -/
noncomputable instance laxMonoidal_pointLowerStar : pointLowerStar.{u}.LaxMonoidal := by
  unfold pointLowerStar
  infer_instance

/-- The inverse image `p^*` is oplax monoidal, being left adjoint to the lax monoidal `p_*`. -/
noncomputable instance oplaxMonoidal_pointUpperStar : pointUpperStar.{u}.OplaxMonoidal :=
  pointUpperStarLowerStarAdjunction.leftAdjointOplaxMonoidal

/-- The inverse image `p^*` preserves the unit. See the module docstring. -/
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u}) := by
  unfold pointUpperStar
  infer_instance

/-- The inverse image `p^*` commutes with the tensor product. See the module docstring. -/
instance isIso_δ_pointUpperStar (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    IsIso (δ pointUpperStar F G) := by
  unfold pointUpperStar
  infer_instance

/-- The inverse image `p^*` is strong monoidal. -/
noncomputable instance monoidal_pointUpperStar : pointUpperStar.{u}.Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

/-- The direct image `p_*` is lax braided, being the pushforward along a continuous functor. -/
noncomputable instance laxBraided_pointLowerStar : pointLowerStar.{u}.LaxBraided := by
  unfold pointLowerStar
  infer_instance

/-- The inverse image `p^*` is lax braided (hence braided, being strong monoidal): the
compatibility with the braiding is the mate of the one of `p_*`. In particular `p^*` sends
commutative ring objects to commutative ring objects. -/
noncomputable instance laxBraided_pointUpperStar : pointUpperStar.{u}.LaxBraided where
  braided F G := by
    have h : δ pointUpperStar F G ≫ (β_ (pointUpperStar.obj F) (pointUpperStar.obj G)).hom =
        pointUpperStar.map (β_ F G).hom ≫ δ pointUpperStar G F := by
      change (pointUpperStarLowerStarAdjunction.homEquiv _ _).symm
          ((pointUpperStarLowerStarAdjunction.unit.app F ⊗ₘ
            pointUpperStarLowerStarAdjunction.unit.app G) ≫ μ pointLowerStar _ _) ≫ _ =
        _ ≫ (pointUpperStarLowerStarAdjunction.homEquiv _ _).symm
          ((pointUpperStarLowerStarAdjunction.unit.app G ⊗ₘ
            pointUpperStarLowerStarAdjunction.unit.app F) ≫ μ pointLowerStar _ _)
      rw [← Adjunction.homEquiv_naturality_right_symm]
      erw [← Adjunction.homEquiv_naturality_left_symm]
      rw [Category.assoc, Functor.LaxBraided.braided]
      erw [BraidedCategory.braiding_naturality_assoc]
      rfl
    rw [← cancel_epi (δ pointUpperStar F G), Functor.Monoidal.δ_μ_assoc, reassoc_of% h,
      Functor.Monoidal.δ_μ, Category.comp_id]

/-! ### The inverse image `p_X^*` and the coefficient rings `Λ_X` -/

/-- The inverse image `p_X^* = π_X^* ∘ p^*` from condensed abelian groups to abelian sheaves on
`X_proét`. On the test objects it is the inverse image along `S ↦ X[S]`. -/
noncomputable def upperStarFromPoint (X : Scheme.{u}) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  pointUpperStar ⋙ (toSpecZ X)^*[Ab.{u + 1}]

/-- The inverse image `p_X^*` is strong monoidal. -/
noncomputable instance monoidal_upperStarFromPoint (X : Scheme.{u}) :
    (upperStarFromPoint X).Monoidal := by
  unfold upperStarFromPoint
  infer_instance

/-- The inverse image `p_X^*` is lax braided. In particular it sends commutative ring objects to
commutative ring objects. -/
noncomputable instance laxBraided_upperStarFromPoint (X : Scheme.{u}) :
    (upperStarFromPoint X).LaxBraided := by
  unfold upperStarFromPoint
  infer_instance

/-- The coefficient ring `Λ_X = p_X^* Λ` on `X_proét` of a condensed ring `Λ`. -/
noncomputable def coefficientRing (X : Scheme.{u})
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    Mon (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  (upperStarFromPoint X).mapMon.obj Λ

lemma coefficientRing_X (X : Scheme.{u})
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (coefficientRing X Λ).X = (upperStarFromPoint X).obj Λ.X :=
  rfl

/-- The condensed ring `T̲ = C(-, T)` of continuous maps into a topological ring `T`, as a ring
object of condensed abelian groups. -/
noncomputable def continuousMapCondensedRing (T : Type) [TopologicalSpace T] [Ring T]
    [IsTopologicalRing T] : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Mon.mk (Profinite.continuousMapRingObj T)

/-! ### The comparison `α_f : f^* Λ_Y ≅ Λ_X` -/

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The natural isomorphism `f^* ∘ p_Y^* ≅ p_X^*`: the composition isomorphism
`f^* ∘ π_Y^* ≅ (f ≫ π_Y)^*` of the pullbacks, followed by `f ≫ π_Y = π_X`. On the test objects
it is the canonical isomorphism `X ×_Y Y[S] ≅ X[S]`. -/
noncomputable def upperStarFromPointComp :
    upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}] ≅ upperStarFromPoint X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft pointUpperStar
    ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
      eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f)))

/-- The comparison `f^* ∘ p_Y^* ≅ p_X^*` is a monoidal natural isomorphism. See the module
docstring. -/
instance isMonoidal_upperStarFromPointComp :
    NatTrans.IsMonoidal (upperStarFromPointComp f).hom := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ toSpecZ Y))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y)).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  have hr : NatTrans.IsMonoidal (lowerStarComp Ab.{u + 1} f (toSpecZ Y)).hom := by
    unfold lowerStarComp
    infer_instance
  have hc : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f (toSpecZ Y)).inv :=
    isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} f (toSpecZ Y)).inv
  have he (g g' : X ⟶ specZ.{u}) (h : g = g') : NatTrans.IsMonoidal
      (eqToIso (congrArg (upperStar Ab.{u + 1}) h)).hom := by
    subst g'
    exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))
  have := he (f ≫ toSpecZ Y) (toSpecZ X) (comp_toSpecZ f)
  unfold upperStarFromPointComp
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance

/-- The comparison `α_f : f^* Λ_Y ≅ Λ_X` of the coefficient rings pulled back from the point,
an isomorphism of ring objects of abelian sheaves on `X_proét`. -/
noncomputable def coefficientPullbackIso
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (f)^*[Ab.{u + 1}].mapMon.obj (coefficientRing Y Λ) ≅ coefficientRing X Λ :=
  (Functor.mapMonCompIso (F := upperStarFromPoint Y) (G := (f)^*[Ab.{u + 1}])).symm.app Λ ≪≫
    (Functor.mapMonNatIso (upperStarFromPointComp f)).app Λ

end Comparison

/-! ### The canonical coefficient morphisms of the six functors on module objects -/

section CoefficientMorphisms

open MonObj

open scoped CategoryTheory.Obj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-! ### The coefficient ring objects `Λ_X` -/

/-- The coefficient ring object `Λ_X = p_X^* Λ` of abelian sheaves on `X_proét`, with the ring
object structure transported along the strong monoidal functor `p_X^*`. -/
noncomputable abbrev condensedRingObj (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (upperStarFromPoint X).obj Λ

/-- The coefficient ring object `Λ_X` is commutative when `Λ` is, `p_X^*` being braided. -/
instance isCommMonObj_condensedRingObj [IsCommMonObj Λ] (X : Scheme.{u}) :
    IsCommMonObj (condensedRingObj Λ X) :=
  Functor.isCommMonObj_obj (F := upperStarFromPoint X)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The canonical coefficient morphisms -/

/-- The canonical coefficient morphism `α_f : f^* Λ_Y ⟶ Λ_X`: the component at `Λ` of the
comparison isomorphism `f^* ∘ p_Y^* ≅ p_X^*`, which on the test objects is the canonical
isomorphism `X ×_Y Y[S] ≅ X[S]`. -/
noncomputable abbrev condensedPullbackHom :
    (f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y) ⟶ condensedRingObj Λ X :=
  Functor.compAlgHom (upperStarFromPoint Y) (f)^*[Ab.{u + 1}] (upperStarFromPointComp f).hom Λ

/-- `α_f` is a morphism of ring objects. -/
instance isMonHom_condensedPullbackHom : IsMonHom (condensedPullbackHom Λ f) :=
  Functor.isMonHom_compAlgHom _ _ _ _

/-- `α_f` is an isomorphism, for every morphism of schemes `f`. -/
instance isIso_condensedPullbackHom : IsIso (condensedPullbackHom Λ f) :=
  inferInstanceAs (IsIso ((upperStarFromPointComp f).hom.app Λ))

omit [MonObj Λ] in
/-- For an open immersion `j : U ⟶ X`, `α_j : j^* Λ_X ⟶ Λ_U` is an isomorphism. This is the
special case of `ProEtale.isIso_condensedPullbackHom` used by the exceptional operations. -/
lemma isIso_condensedPullbackHom_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (condensedPullbackHom Λ j) :=
  inferInstance

/-- The canonical coefficient morphism `η_f : Λ_Y ⟶ f_* Λ_X`: the mate of `α_f` under the
adjunction `f^* ⊣ f_*`, the unit `Λ_Y ⟶ f_* f^* Λ_Y` followed by `f_* α_f`. -/
noncomputable def condensedPushforwardHom :
    condensedRingObj Λ Y ⟶ (f)_*[Ab.{u + 1}].obj (condensedRingObj Λ X) :=
  (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y) ≫
    (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f)

/-- `η_f` is a morphism of ring objects, for the ring object structure of `f_* Λ_X` induced by
the lax monoidal structure of `f_*`. -/
instance isMonHom_condensedPushforwardHom : IsMonHom (condensedPushforwardHom Λ f) :=
  inferInstanceAs (IsMonHom
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y) ≫
      (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f)))

omit [MonObj Λ] in
/-- `η_f` is the mate of `α_f`: it is the unit `Λ_Y ⟶ f_* f^* Λ_Y` followed by `f_* α_f`. -/
@[reassoc]
lemma unitAlgHom_comp_map_condensedPullbackHom :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y) ≫
      (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f) =
        condensedPushforwardHom Λ f :=
  rfl

omit [MonObj Λ] in
/-- The canonical coefficient morphism `α_f` is the composition isomorphism
`f^* π_Y^* ≅ (f ≫ π_Y)^*` of the pullbacks, followed by `f ≫ π_Y = π_X`, at `p^* Λ`. -/
lemma condensedPullbackHom_eq :
    condensedPullbackHom Λ f =
      (upperStarComp Ab.{u + 1} f (toSpecZ Y)).inv.app (pointUpperStar.obj Λ) ≫
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f))).app
          (pointUpperStar.obj Λ) := by
  have h₁ : condensedPullbackHom Λ f = (upperStarFromPointComp f).hom.app Λ := rfl
  have h₂ : upperStarFromPointComp f =
      Functor.associator pointUpperStar (toSpecZ Y)^*[Ab.{u + 1}] (f)^*[Ab.{u + 1}] ≪≫
        Functor.isoWhiskerLeft pointUpperStar ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
          eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f))) := by
    unfold upperStarFromPointComp
    rfl
  rw [h₁, h₂]
  exact associator_isoWhiskerLeft_upperStarComp_hom_app Ab.{u + 1} pointUpperStar f _ _
    (comp_toSpecZ f) Λ

omit [MonObj Λ] in
/-- `η` of the identity is the identification `Λ_X ≅ (𝟙 X)_* Λ_X`. -/
lemma condensedPushforwardHom_id (X : Scheme.{u}) :
    condensedPushforwardHom Λ (𝟙 X) =
      (ProEtale.lowerStarId Ab.{u + 1} X).inv.app (condensedRingObj Λ X) := by
  rw [condensedPushforwardHom, condensedPullbackHom_eq]
  exact unitCompUpperStarComp_id Ab.{u + 1} (toSpecZ X) (comp_toSpecZ (𝟙 X))
    (pointUpperStar.obj Λ)

omit [MonObj Λ] in
/-- `η` of a composition is the composition of the `η`'s, up to the composition isomorphism
`g_* ∘ f_* ≅ (f ≫ g)_*`. -/
lemma condensedPushforwardHom_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    condensedPushforwardHom Λ (f ≫ g) =
      condensedPushforwardHom Λ g ≫ (g)_*[Ab.{u + 1}].map (condensedPushforwardHom Λ f) ≫
        (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app (condensedRingObj Λ X) := by
  rw [condensedPushforwardHom, condensedPushforwardHom, condensedPushforwardHom,
    condensedPullbackHom_eq, condensedPullbackHom_eq, condensedPullbackHom_eq]
  exact unitCompUpperStarComp_comp Ab.{u + 1} f g (toSpecZ X) (toSpecZ Y) (toSpecZ Z)
    (comp_toSpecZ f) (comp_toSpecZ g) (comp_toSpecZ (f ≫ g)) (pointUpperStar.obj Λ)

end CoefficientMorphisms

end AlgebraicGeometry.ProEtale
