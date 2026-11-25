/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpen
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseUniversalCover

/-!
# Monodromy of lisse sheaves and pullback

Let `f : Y' ⟶ Y` be a morphism of connected schemes. The monodromies of lisse `ℓ`-adic sheaves
on `Y` and `Y'` (`AlgebraicGeometry.ProEtale.LisseMonodromy`) are *compatible* with `f`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`) if, under the identification
`G_{y ≫ f} = (f^* G)_y` of stalks, the transport along the path `F_{y ≫ f} ≅ F_{z ≫ f}` induced by
a path `τ : F_y ≅ F_z` of `Y'` is the transport along `τ` on `Y'`: the monodromy representation
of `π₁(Y', y)` on `(f^* G)_y` is that of `π₁(Y, y ≫ f)` on `G_{y ≫ f}`, restricted along the map
of fundamental groups. This is the compatibility of
`proposition-lattices-representations-normal-scheme` with base change of finite étale covers
(`thm-galois-fundamental`); its existence, for connected normal Noetherian schemes, is
`AlgebraicGeometry.ProEtale.exists_lisseMonodromy_isCompatible_of_isIntegrallyClosed_stalk` (for
regular ones, `AlgebraicGeometry.ProEtale.exists_lisseMonodromy_isCompatible`).

If moreover `π₁(Y') → π₁(Y)` is surjective, a lisse subsheaf `G'` of `f^* N` for a lisse `N`
on `Y` is the pullback of a lisse sheaf on `Y`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_injective`): its stalk is a
`π₁(Y')`-stable, hence `π₁(Y)`-stable, subspace of `N_{y ≫ f}`.

## Main statements

- `AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`: compatibility of monodromies with a
  morphism.
- `AlgebraicGeometry.ProEtale.exists_lisseMonodromy_isCompatible_of_isIntegrallyClosed_stalk`:
  compatible monodromies exist.
- `AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_injective`: lisse subsheaves
  of pullbacks descend along a morphism surjective on fundamental groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme.FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω]

namespace LisseMonodromy

/-- The monodromies `M` on `Y` and `M'` on `Y'` are *compatible* with `f : Y' ⟶ Y` if the
transport along the path `F_{y ≫ f} ≅ F_{z ≫ f}` induced by a path `τ : F_y ≅ F_z` of `Y'` is,
under the identifications `G_{y ≫ f} = (f^* G)_y`, the transport along `τ` of the pullback. -/
def IsCompatible (f : Y' ⟶ Y) (M : LisseMonodromy l Y Ω) (M' : LisseMonodromy l Y' Ω) : Prop :=
  ∀ ⦃y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'⦄ (τ : fiber y ≅ fiber z) (G : LisseSheaf l Y),
    (M.mono (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
      (upperStarStalkIso l f y G.obj.X).hom ≫ (M'.mono τ).hom.app (G.upperStar l f)

/-- The `ℚ̄_ℓ`-linear identification `G_{y ≫ f} ≅ (f^* G)_y` of stalks. -/
noncomputable abbrev upperStarStalkLinearEquiv (f : Y' ⟶ Y)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y') (G : LisseSheaf l Y) :
    StalkSpace (y ≫ f) G ≃ₗ[PadicAlgCl l] StalkSpace y (G.upperStar l f) :=
  WeilCoefficients.linearEquivOfIso (upperStarStalkIso l f y G.obj.X)

variable {f : Y' ⟶ Y} {M : LisseMonodromy l Y Ω} {M' : LisseMonodromy l Y' Ω}

/-- For compatible monodromies, the identification `G_{y ≫ f} ≅ (f^* G)_y` intertwines the
action of `π₁(Y', y)` on `(f^* G)_y` with that of its image in `π₁(Y, y ≫ f)` on `G_{y ≫ f}`. -/
lemma IsCompatible.rep_apply (hc : IsCompatible f M M')
    {y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'} (σ : Aut (fiber y)) (G : LisseSheaf l Y)
    (v : StalkSpace (y ≫ f) G) :
    upperStarStalkLinearEquiv f y G (M.rep (y ≫ f) G (Aut.of (pullbackPathIso f σ.asIso)) v) =
      M'.rep y (G.upperStar l f) σ (upperStarStalkLinearEquiv f y G v) := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) (hc σ.asIso G)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The stalks of a lisse sheaf at geometric points are finite-dimensional. -/
instance finiteDimensional_stalkSpace (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (G : LisseSheaf l Y) : FiniteDimensional (PadicAlgCl l) (StalkSpace t G) :=
  (G.property.upperStar t).isAdicConstructibleSheaf.finiteDimensional_globalSections

/-- **Lisse subsheaves of pullbacks descend.** Let `M`, `M'` be monodromies on `Y`, `Y'`
compatible with `f : Y' ⟶ Y`, which are equivalences at `t ≫ f` and `t`, and assume that every
automorphism of `F_{t ≫ f}` is induced by one of `F_t` (`π₁(Y', t) → π₁(Y, t ≫ f)` is
surjective). Let `N` be lisse on `Y` and `i : G' ⟶ f^* N` a morphism of lisse sheaves on `Y'`
which is injective on stalks at `t`. Then `G'` is the pullback of a lisse sheaf on `Y`: the image
of `G'_t` in `(f^* N)_t = N_{t ≫ f}` is `π₁(Y')`-stable, hence `π₁(Y)`-stable, hence the stalk
of a lisse sheaf `G` on `Y`, and `f^* G ≅ G'` since both have the same `π₁(Y')`-representation. -/
theorem exists_upperStar_iso_of_injective {t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'}
    (hM : M.IsEquivalenceAt (t ≫ f)) (hM' : M'.IsEquivalenceAt t) (hc : IsCompatible f M M')
    (hsurj : ∀ σ : Aut (fiber (t ≫ f)), ∃ σ' : Aut (fiber t),
      Aut.of (pullbackPathIso f σ'.asIso) = σ)
    {N : LisseSheaf l Y} {G' : LisseSheaf l Y'} (i : G' ⟶ N.upperStar l f)
    (hi : Function.Injective ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map i)).hom) :
    ∃ G : LisseSheaf l Y, Nonempty (G.upperStar l f ≅ G') := by
  set ι := ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map i)).hom
  set e₀ := upperStarStalkLinearEquiv f t N
  let W : Subrepresentation (M.rep (t ≫ f) N) :=
    { toSubmodule := (LinearMap.range ι).comap e₀.toLinearMap
      apply_mem_toSubmodule σ b hb := by
        obtain ⟨σ', rfl⟩ := hsurj σ
        obtain ⟨g, hg⟩ := hb
        refine ⟨M'.rep t G' σ' g, ?_⟩
        rw [LinearEquiv.coe_toLinearMap, hc.rep_apply, ← LinearEquiv.coe_toLinearMap, ← hg]
        exact M'.rep_naturality t i σ' g }
  obtain ⟨G, eG, heG⟩ := hM.essSurj W.toSubmodule W.toRepresentation fun φ w ↦ by
    obtain ⟨φ', hφ'⟩ := LinearMap.exists_extend (K := PadicAlgCl l) (p := W.toSubmodule) φ
    have h (σ : Aut (fiber (t ≫ f))) : φ (W.toRepresentation σ w) = φ' (M.rep _ N σ w) := by
      rw [← hφ']
      rfl
    simp_rw [h]
    exact hM.continuous_rep N φ' w
  -- the image of `G'_t` in `(f^* N)_t`
  have key (x : LinearMap.range ι) : ι ((LinearEquiv.ofInjective ι hi).symm x) = x := by
    rw [← LinearEquiv.ofInjective_apply ι (h := hi), LinearEquiv.apply_symm_apply]
  let ψ : StalkSpace t (G.upperStar l f) →ₗ[PadicAlgCl l] StalkSpace t G' :=
    (LinearEquiv.ofInjective ι hi).symm.toLinearMap ∘ₗ
      ((e₀.toLinearMap ∘ₗ W.toSubmodule.subtype).codRestrict (LinearMap.range ι) fun w ↦ w.2) ∘ₗ
      eG.toLinearMap ∘ₗ (upperStarStalkLinearEquiv f t G).symm.toLinearMap
  have hψ (v) : ι (ψ v) = e₀ (eG ((upperStarStalkLinearEquiv f t G).symm v)) :=
    key _
  have hψinj : Function.Injective ψ := fun v w h ↦ by
    have := congrArg ι h
    rw [hψ, hψ] at this
    exact (upperStarStalkLinearEquiv f t G).symm.injective
      (eG.injective (Subtype.ext (e₀.injective this)))
  have hψsurj : Function.Surjective ψ := fun g ↦ by
    obtain ⟨w, hw⟩ := eG.surjective ⟨e₀.symm (ι g), g, (e₀.apply_symm_apply (ι g)).symm⟩
    refine ⟨upperStarStalkLinearEquiv f t G w, hi ?_⟩
    rw [hψ, LinearEquiv.symm_apply_apply, hw, LinearEquiv.apply_symm_apply]
  obtain ⟨φ, hφ⟩ := hM'.full ψ fun σ v ↦ hi (by
    rw [hψ, M'.rep_naturality t i σ, hψ]
    obtain ⟨v, rfl⟩ := (upperStarStalkLinearEquiv f t G).surjective v
    rw [← hc.rep_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, heG,
      ← hc.rep_apply]
    rfl)
  have := hM'.isIso_of_bijective φ (by rw [hφ]; exact ⟨hψinj, hψsurj⟩)
  exact ⟨G, ⟨asIso φ⟩⟩

end LisseMonodromy

/-- **Compatible monodromies exist** (blueprint:
`proposition-lattices-representations-normal-scheme`, with the compatibility of
`thm-galois-fundamental` with base change). For a morphism `f : Y' ⟶ Y` of connected normal
Noetherian schemes there are monodromies of lisse `ℓ`-adic sheaves on `Y` and on `Y'` which are
equivalences at every base point
(`AlgebraicGeometry.ProEtale.exists_lisseMonodromy_of_isIntegrallyClosed_stalk`) and are compatible
with `f`: the equivalence of `proposition-lattices-representations-normal-scheme` is built from the
fibre functors on finite étale covers, and pulling back finite étale covers along `f` is compatible
with the fibre functors (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackFiberIso`), so the monodromy
action of `π₁(Y', y)` on `(f^* G)_y` is that of `π₁(Y, y ≫ f)` on `G_{y ≫ f}` restricted along
`π₁(Y', y) → π₁(Y, y ≫ f)`. -/
theorem exists_lisseMonodromy_isCompatible_of_isIntegrallyClosed_stalk [IsLocallyNoetherian Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    [IsLocallyNoetherian Y'] [CompactSpace Y'] [ConnectedSpace Y']
    (hY' : ∀ y : Y', IsDomain (Y'.presheaf.stalk y) ∧ IsIntegrallyClosed (Y'.presheaf.stalk y))
    (f : Y' ⟶ Y) :
    ∃ (M : LisseMonodromy l Y Ω) (M' : LisseMonodromy l Y' Ω), (∀ t, M.IsEquivalenceAt t) ∧
      (∀ t, M'.IsEquivalenceAt t) ∧ LisseMonodromy.IsCompatible f M M' := by
  have := irreducibleSpace_of_isDomain_stalk Y fun y ↦ (hY y).1
  have := irreducibleSpace_of_isDomain_stalk Y' fun y ↦ (hY' y).1
  have hU (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :=
    IsAdicLisseSheaf.exists_iso_upperStar_universalCover_of_isIntegrallyClosed_stalk hY
      (Scheme.universalCovers Y Ω) y G.property
  have hU' (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y') (G : LisseSheaf l Y') :=
    IsAdicLisseSheaf.exists_iso_upperStar_universalCover_of_isIntegrallyClosed_stalk hY'
      (Scheme.universalCovers Y' Ω) y G.property
  exact ⟨_, _, Scheme.UniversalCovers.lisseMonodromy_isEquivalenceAt_of_irreducibleSpace hU,
    Scheme.UniversalCovers.lisseMonodromy_isEquivalenceAt_of_irreducibleSpace hU',
    fun _ _ τ G ↦ (Scheme.universalCoversHom f).lisseMonodromy_mono_upperStar hU hU' τ G⟩

/-- **Compatible monodromies exist** for a morphism `f : Y' ⟶ Y` of connected regular Noetherian
schemes: regular schemes are normal
(`AlgebraicGeometry.ProEtale.exists_lisseMonodromy_isCompatible_of_isIntegrallyClosed_stalk`). -/
theorem exists_lisseMonodromy_isCompatible [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y]
    [ConnectedSpace Y] [IsLocallyNoetherian Y'] [CompactSpace Y'] [IsRegular Y']
    [ConnectedSpace Y'] (f : Y' ⟶ Y) :
    ∃ (M : LisseMonodromy l Y Ω) (M' : LisseMonodromy l Y' Ω), (∀ t, M.IsEquivalenceAt t) ∧
      (∀ t, M'.IsEquivalenceAt t) ∧ LisseMonodromy.IsCompatible f M M' :=
  exists_lisseMonodromy_isCompatible_of_isIntegrallyClosed_stalk
    (fun _ ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk _⟩)
    (fun _ ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk _⟩) f

section DenseOpen


/-- A nonempty open subscheme of a connected normal locally Noetherian scheme is again
connected, normal and locally Noetherian. -/
lemma isLocallyNoetherian_isIntegrallyClosed_stalk_connectedSpace_of_isOpenImmersion
    [IsLocallyNoetherian Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (j : Y' ⟶ Y) [IsOpenImmersion j] [Nonempty Y'] :
    IsLocallyNoetherian Y' ∧
      (∀ y : Y', IsDomain (Y'.presheaf.stalk y) ∧ IsIntegrallyClosed (Y'.presheaf.stalk y)) ∧
        ConnectedSpace Y' := by
  have := irreducibleSpace_of_isDomain_stalk Y fun y ↦ (hY y).1
  exact ⟨isLocallyNoetherian_of_isOpenImmersion j,
    Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain j hY,
    Scheme.FiniteEtale.connectedSpace_of_isOpenImmersion j⟩

/-- A nonempty open subscheme of a connected regular locally Noetherian scheme is again
connected, regular and locally Noetherian. -/
lemma isLocallyNoetherian_isRegular_connectedSpace_of_isOpenImmersion [IsLocallyNoetherian Y]
    [IsRegular Y] [ConnectedSpace Y] (j : Y' ⟶ Y) [IsOpenImmersion j] [Nonempty Y'] :
    IsLocallyNoetherian Y' ∧ IsRegular Y' ∧ ConnectedSpace Y' := by
  have := IsRegular.irreducibleSpace Y
  refine ⟨isLocallyNoetherian_of_isOpenImmersion j,
    ⟨isRegularLocalRing_stalk_of_etale j fun _ ↦ inferInstance⟩,
    Scheme.FiniteEtale.connectedSpace_of_isOpenImmersion j⟩

/-- **The fundamental group of a dense open of a normal scheme surjects**, in terms of paths:
every automorphism of the fibre functor `F_{t ≫ j}` of `Y` is induced by an automorphism of the
fibre functor `F_t` of the nonempty open `Y'` (blueprint `theorem-purity-real-sheaves-curves`,
part (1)). -/
lemma exists_pullbackPathIso_eq_of_isIntegrallyClosed_stalk [IsLocallyNoetherian Y]
    [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (j : Y' ⟶ Y) [IsOpenImmersion j] (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y')
    (σ : Aut (fiber (t ≫ j))) : ∃ σ' : Aut (fiber t),
      Aut.of (pullbackPathIso j σ'.asIso) = σ := by
  have : Nonempty Y' := ⟨t.base (Nonempty.some inferInstance)⟩
  obtain ⟨-, -, _⟩ :=
    isLocallyNoetherian_isIntegrallyClosed_stalk_connectedSpace_of_isOpenImmersion hY j
  obtain ⟨G', _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup t
  obtain ⟨G, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup (t ≫ j)
  obtain ⟨g', hg'⟩ :=
    Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk j
      (pullbackFiberIso j t) G' G hY ((PreGaloisCategory.toAutMulEquiv _ G).symm σ)
  refine ⟨PreGaloisCategory.toAut (fiber t) G' g', ?_⟩
  ext P x
  obtain ⟨y, rfl⟩ : ∃ y, (pullbackFiberIso j t).hom.app P y = x :=
    ⟨(pullbackFiberIso j t).inv.app P x, ConcreteCategory.congr_hom
      ((pullbackFiberIso j t).inv_hom_id_app P) x⟩
  have h := Scheme.FiniteEtale.fundamentalGroupMap_smul (pullbackFiberIso j t) G' G g' P y
  rw [hg'] at h
  conv_rhs => rw [← (PreGaloisCategory.toAutMulEquiv _ G).apply_symm_apply σ]
  rw [PreGaloisCategory.toAutMulEquiv_apply, PreGaloisCategory.toAut_hom_app_apply, h]
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply ((pullbackFiberIso j t).hom.app P), Iso.hom_inv_id_app,
    ConcreteCategory.id_apply]
  rfl

/-- **The fundamental group of a dense open of a regular scheme surjects**, in terms of paths
(`AlgebraicGeometry.ProEtale.exists_pullbackPathIso_eq_of_isIntegrallyClosed_stalk`, regular
schemes being normal). -/
lemma exists_pullbackPathIso_eq_of_isRegular [IsLocallyNoetherian Y] [IsRegular Y]
    [ConnectedSpace Y] (j : Y' ⟶ Y) [IsOpenImmersion j] (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y')
    (σ : Aut (fiber (t ≫ j))) : ∃ σ' : Aut (fiber t),
      Aut.of (pullbackPathIso j σ'.asIso) = σ :=
  exists_pullbackPathIso_eq_of_isIntegrallyClosed_stalk
    (fun _ ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk _⟩) j t σ

/-- A nonempty scheme has a geometric point with values in the algebraic closure of a field
(of the residue field at any point). -/
lemma exists_algebraicClosure_point (Y' : Scheme.{u}) [Nonempty Y'] :
    ∃ (Ω : Type u) (_ : Field Ω), Nonempty (Spec (.of (AlgebraicClosure Ω)) ⟶ Y') :=
  let y : Y' := Nonempty.some inferInstance
  ⟨Y'.residueField y, inferInstance, ⟨Spec.map (CommRingCat.ofHom
    (algebraMap (Y'.residueField y) (AlgebraicClosure (Y'.residueField y)))) ≫
      Y'.fromSpecResidueField y⟩⟩

/-- An open subscheme of a Noetherian scheme is quasi-compact. -/
lemma compactSpace_of_isOpenImmersion [IsLocallyNoetherian Y] [CompactSpace Y] (j : Y' ⟶ Y)
    [IsOpenImmersion j] : CompactSpace Y' :=
  have : IsNoetherian Y := {}
  ⟨j.isOpenEmbedding.isInducing.isCompact_iff.2 (TopologicalSpace.NoetherianSpace.isCompact _)⟩

/-- **Lisse subsheaves extend over a dense open** (blueprint `theorem-purity-real-sheaves-curves`,
part (4), geometric form). Let `Y` be a connected normal Noetherian scheme,
`j : Y' ⟶ Y` an open immersion with `Y'` nonempty, and `N` lisse on `Y`. Every lisse subsheaf
`G'` of `j^* N` is the restriction of a lisse sheaf on `Y`: this is
`AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_injective`, the map
`π₁(Y', t) → π₁(Y, t)` being surjective. -/
theorem IsAdicLisseSheaf.exists_upperStar_iso_of_mono_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian Y] [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (j : Y' ⟶ Y) [IsOpenImmersion j] [Nonempty Y'] {N : AdicSheaf l Y} (hN : IsAdicLisseSheaf N)
    {G' : AdicSheaf l Y'} (hG' : IsAdicLisseSheaf G') (i : G' ⟶ (j)^*ᵃ[l].obj N) [Mono i] :
    ∃ G : AdicSheaf l Y, IsAdicLisseSheaf G ∧ Nonempty ((j)^*ᵃ[l].obj G ≅ G') := by
  obtain ⟨Ω, _, ⟨t⟩⟩ := exists_algebraicClosure_point Y'
  obtain ⟨_, hY', _⟩ :=
    isLocallyNoetherian_isIntegrallyClosed_stalk_connectedSpace_of_isOpenImmersion hY j
  have := compactSpace_of_isOpenImmersion j
  obtain ⟨M, M', hM, hM', hc⟩ :=
    exists_lisseMonodromy_isCompatible_of_isIntegrallyClosed_stalk (l := l) (Ω := Ω) hY hY' j
  have : (stalkFunctor l t).PreservesMonomorphisms := by
    unfold stalkFunctor
    infer_instance
  obtain ⟨G, ⟨e⟩⟩ := LisseMonodromy.exists_upperStar_iso_of_injective (hM (t ≫ j)) (hM' t) hc
    (exists_pullbackPathIso_eq_of_isIntegrallyClosed_stalk hY j t) (N := ⟨N, hN⟩)
    (G' := ⟨G', hG'⟩)
    (ObjectProperty.homMk i)
    ((ModuleCat.mono_iff_injective _).1 ((WeilCoefficients.toModuleCat l).map_mono
      ((stalkFunctor l t).map ((AdicSheaf.forget Y').map i))))
  exact ⟨G.obj, G.property, ⟨(ObjectProperty.ι _).mapIso e⟩⟩

/-- **Lisse subsheaves extend over a dense open** of a connected regular Noetherian scheme:
regular schemes are normal
(`IsAdicLisseSheaf.exists_upperStar_iso_of_mono_of_isIntegrallyClosed_stalk`). -/
theorem IsAdicLisseSheaf.exists_upperStar_iso_of_mono [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsRegular Y] [ConnectedSpace Y] (j : Y' ⟶ Y) [IsOpenImmersion j] [Nonempty Y']
    {N : AdicSheaf l Y} (hN : IsAdicLisseSheaf N) {G' : AdicSheaf l Y'}
    (hG' : IsAdicLisseSheaf G') (i : G' ⟶ (j)^*ᵃ[l].obj N) [Mono i] :
    ∃ G : AdicSheaf l Y, IsAdicLisseSheaf G ∧ Nonempty ((j)^*ᵃ[l].obj G ≅ G') :=
  IsAdicLisseSheaf.exists_upperStar_iso_of_mono_of_isIntegrallyClosed_stalk
    (fun _ ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk _⟩) j hN hG' i

/-- The direct image `j_* G'` of a lisse subsheaf `G'` of the restriction `j^* N` of a lisse
sheaf `N` to a dense open `j : Y' ⟶ Y` of a connected normal Noetherian scheme is
lisse: `G'` is the restriction of a lisse `G`
(`IsAdicLisseSheaf.exists_upperStar_iso_of_mono_of_isIntegrallyClosed_stalk`), and
`G ≅ j_* j^* G`
(`IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed`). -/
theorem IsAdicLisseSheaf.adicLowerStar_of_mono_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian Y] [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (j : Y' ⟶ Y) [IsOpenImmersion j] [Nonempty Y'] (hj : Dense (Set.range j))
    {N : AdicSheaf l Y} (hN : IsAdicLisseSheaf N) {G' : AdicSheaf l Y'}
    (hG' : IsAdicLisseSheaf G') (i : G' ⟶ (j)^*ᵃ[l].obj N) [Mono i] :
    IsAdicLisseSheaf ((j)_*ᵃ[l].obj G') := by
  obtain ⟨G, hG, ⟨e⟩⟩ := hN.exists_upperStar_iso_of_mono_of_isIntegrallyClosed_stalk hY j hG' i
  have := hG.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed hY j hj
  exact hG.of_iso (asIso ((adicUpperStarLowerStarAdjunction l j).unit.app G) ≪≫
    (j)_*ᵃ[l].mapIso e)

/-- The direct image `j_* G'` of a lisse subsheaf `G'` of the restriction `j^* N` of a lisse
sheaf `N` to a dense open `j : Y' ⟶ Y` of a connected regular Noetherian scheme is lisse:
regular schemes are normal (`IsAdicLisseSheaf.adicLowerStar_of_mono_of_isIntegrallyClosed_stalk`).
-/
theorem IsAdicLisseSheaf.adicLowerStar_of_mono [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsRegular Y] [ConnectedSpace Y] (j : Y' ⟶ Y) [IsOpenImmersion j] [Nonempty Y']
    (hj : Dense (Set.range j)) {N : AdicSheaf l Y} (hN : IsAdicLisseSheaf N)
    {G' : AdicSheaf l Y'} (hG' : IsAdicLisseSheaf G') (i : G' ⟶ (j)^*ᵃ[l].obj N) [Mono i] :
    IsAdicLisseSheaf ((j)_*ᵃ[l].obj G') :=
  IsAdicLisseSheaf.adicLowerStar_of_mono_of_isIntegrallyClosed_stalk
    (fun _ ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk _⟩) j hj hN hG' i

/-- **Restriction to a dense open is fully faithful on lisse sheaves** (blueprint
`theorem-purity-real-sheaves-curves`, part (4), geometric form): for a dense open
`j : Y' ⟶ Y` of a scheme whose local rings are integrally closed domains and `N` lisse on `Y`,
the restriction `Hom(A, N) → Hom(j^* A, j^* N)` is bijective for every `A`, since the unit
`N ⟶ j_* j^* N` is an isomorphism. -/
theorem IsAdicLisseSheaf.adicUpperStar_map_bijective_of_isIntegrallyClosed_stalk
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (j : Y' ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] (hj : Dense (Set.range j))
    (A : AdicSheaf l Y) {N : AdicSheaf l Y} (hN : IsAdicLisseSheaf N) :
    Function.Bijective ((j)^*ᵃ[l].map : (A ⟶ N) → ((j)^*ᵃ[l].obj A ⟶ (j)^*ᵃ[l].obj N)) :=
  have := hN.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed hY j hj
  (adicUpperStarLowerStarAdjunction l j).map_bijective_of_isIso_unit_app A

/-- **Restriction to a dense open is fully faithful on lisse sheaves** (blueprint
`theorem-purity-real-sheaves-curves`, part (4), geometric form): for a dense open
`j : Y' ⟶ Y` of a scheme with regular local rings and `N` lisse on `Y`, the restriction
`Hom(A, N) → Hom(j^* A, j^* N)` is bijective for every `A`, since the unit `N ⟶ j_* j^* N` is
an isomorphism. -/
theorem IsAdicLisseSheaf.adicUpperStar_map_bijective
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (j : Y' ⟶ Y) [IsOpenImmersion j]
    [QuasiCompact j] (hj : Dense (Set.range j)) (A : AdicSheaf l Y) {N : AdicSheaf l Y}
    (hN : IsAdicLisseSheaf N) :
    Function.Bijective ((j)^*ᵃ[l].map : (A ⟶ N) → ((j)^*ᵃ[l].obj A ⟶ (j)^*ᵃ[l].obj N)) :=
  have := hN.isIso_adicUpperStarLowerStarAdjunction_unit_app hY j hj
  (adicUpperStarLowerStarAdjunction l j).map_bijective_of_isIso_unit_app A

/-- **Restriction to a dense open preserves irreducible local systems** (blueprint
`theorem-purity-real-sheaves-curves`, part (4), geometric form). Let `Y` be a connected normal
Noetherian scheme and `j : Y' ⟶ Y` a dense open immersion. If `N` is an irreducible
`ℓ`-adic local system on `Y`, so is `j^* N`: it is nonzero since `N ≅ j_* j^* N`, a lisse
subsheaf of `j^* N` is the restriction of a lisse `G`
(`IsAdicLisseSheaf.exists_upperStar_iso_of_mono_of_isIntegrallyClosed_stalk`), and the inclusion
is the restriction of a monomorphism `G ⟶ N` by full faithfulness. -/
theorem IsIrreducibleAdicLocalSystem.adicUpperStar_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian Y] [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (j : Y' ⟶ Y) [IsOpenImmersion j] (hj : Dense (Set.range j)) {N : AdicSheaf l Y}
    (hN : IsIrreducibleAdicLocalSystem N) : IsIrreducibleAdicLocalSystem ((j)^*ᵃ[l].obj N) := by
  obtain ⟨hNl, hN0, hNirr⟩ := hN
  have hjN : ¬ IsZero ((j)^*ᵃ[l].obj N) := fun h ↦ hN0 (by
    have := hNl.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed hY j hj
    exact ((j)_*ᵃ[l].map_isZero h).of_iso
      (asIso ((adicUpperStarLowerStarAdjunction l j).unit.app N)))
  have : Nonempty Y' := not_isEmpty_iff.1 fun _ ↦ hjN (isZero_adicSheaf_of_isEmpty l _)
  refine ⟨hNl.upperStar j, hjN, fun G' i _ hG' ↦ ?_⟩
  obtain ⟨G, hG, ⟨e⟩⟩ := hNl.exists_upperStar_iso_of_mono_of_isIntegrallyClosed_stalk hY j hG' i
  obtain ⟨g, hg⟩ :=
    (hNl.adicUpperStar_map_bijective_of_isIntegrallyClosed_stalk hY j hj G).2 (e.hom ≫ i)
  have : Mono ((j)^*ᵃ[l].map g) := by
    rw [hg]
    infer_instance
  have : Mono g := ⟨fun a b hab ↦
    (hG.adicUpperStar_map_bijective_of_isIntegrallyClosed_stalk hY j hj _).1 (by
      rw [← cancel_mono ((j)^*ᵃ[l].map g), ← Functor.map_comp, ← Functor.map_comp, hab])⟩
  obtain h | h := hNirr G g inferInstance hG
  · exact Or.inl (((j)^*ᵃ[l].map_isZero h).of_iso e.symm)
  · have : IsIso (e.hom ≫ i) := by
      rw [← hg]
      infer_instance
    exact Or.inr (IsIso.of_isIso_comp_left e.hom i)

/-- **Restriction to a dense open preserves irreducible local systems** on a connected regular
Noetherian scheme: regular schemes are normal
(`IsIrreducibleAdicLocalSystem.adicUpperStar_of_isIntegrallyClosed_stalk`). -/
theorem IsIrreducibleAdicLocalSystem.adicUpperStar [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsRegular Y] [ConnectedSpace Y] (j : Y' ⟶ Y) [IsOpenImmersion j] (hj : Dense (Set.range j))
    {N : AdicSheaf l Y} (hN : IsIrreducibleAdicLocalSystem N) :
    IsIrreducibleAdicLocalSystem ((j)^*ᵃ[l].obj N) :=
  IsIrreducibleAdicLocalSystem.adicUpperStar_of_isIntegrallyClosed_stalk
    (fun _ ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk _⟩) j hj hN

end DenseOpen

end AlgebraicGeometry.ProEtale
