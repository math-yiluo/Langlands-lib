/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverContinuity
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverRepresentation
public import WeilConjectures.WeilSheaf.StalkTensor
public import WeilConjectures.WeilSheaf.LisseDuality

/-!
# The monodromy from universal covers is an equivalence

Let `Y` be an irreducible scheme (e.g. a connected normal or regular Noetherian scheme) with
universal profinite étale covers `Ỹ_y` on which lisse sheaves are free, and let `M` be the
monodromy of lisse sheaves obtained from them
(`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy`). At every base point `t`, the stalk
functor identifies lisse sheaves with continuous finite-dimensional representations of
`π₁(Y, t)`
(`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy_isEquivalenceAt_of_irreducibleSpace`):

- the stalk functor is faithful
  (`AlgebraicGeometry.Scheme.UniversalCovers.lisseStalk_faithful_of_irreducibleSpace`):
  on the irreducible scheme `Y` a morphism of lisse sheaves vanishing on one stalk vanishes;
- it is full onto equivariant maps
  (`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy_full`): an equivariant map is an
  invariant element of the stalk of the lisse sheaf `𝓗om(G, H)`, which descends to a global
  section (`AlgebraicGeometry.Scheme.UniversalCovers.exists_globalSection_of_invariant`);
- the monodromy representations are continuous
  (`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy_continuous_rep`);
- essential surjectivity (`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy_essSurj`):
  the lisse sheaf attached to a representation is obtained by descent along the universal cover
  (`AlgebraicGeometry.Scheme.UniversalCovers.exists_lisseSheaf_rep`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

section Uncurry

open Functor.LaxMonoidal

variable {l : ℕ} [Fact l.Prime] {Z : Scheme.{u}}

/-- The morphism `G ⟶ H` corresponding to `v : ℚ̄_ℓ ⟶ 𝓗om(G, H)`, on underlying sheaves:
`G ≅ 𝟙 ⊗ G ⟶ 𝓗om(G, H) ⊗ G ⟶ H`. -/
lemma transpose_comp_ihomRegularIso_hom_app_hom {G H : AdicSheaf l Z}
    (v : AdicSheaf.unit l Z ⟶ (AdicSheaf.ihom G).obj H) :
    (Mod.transpose v ≫ Mod.ihomRegularIso.hom.app H).hom =
      (λ_ G.X).inv ≫ (MonObj.one (X := adicConstantSheaf l Z) ≫ v.hom) ▷ G.X ≫
        Mod.evaluation G H := by
  have h₁ := Mod.uncurryHom_transpose v
  rw [Mod.uncurryHom, Mod.uncurryHom, Mod.evaluation_regular] at h₁
  have hunit : (ρ_ H.X).inv ≫ H.X ◁ MonObj.one ≫ Mod.rightAct H = 𝟙 _ := by
    have := congrArg Mod.Hom.hom (Mod.unitRight_rightActHom H)
    rw [Mod.comp_hom', Mod.id_hom'] at this
    change ((ρ_ H.X).inv ≫ H.X ◁ MonObj.one) ≫ Mod.rightAct H = 𝟙 _ at this
    simpa only [Category.assoc] using this
  have e₁ : (ρ_ G.X).inv ≫ G.X ◁ MonObj.one (X := adicConstantSheaf l Z) ≫
      (Mod.transpose v ≫ Mod.ihomRegularIso.hom.app H).hom ▷ adicConstantSheaf l Z =
      (Mod.transpose v ≫ Mod.ihomRegularIso.hom.app H).hom ≫ (ρ_ H.X).inv ≫
        H.X ◁ MonObj.one := by
    rw [whisker_exchange, ← rightUnitor_inv_naturality_assoc]
    rfl
  have e₂ : (ρ_ G.X).inv ≫ G.X ◁ (MonObj.one (X := adicConstantSheaf l Z)) ≫
      (β_ G.X (adicConstantSheaf l Z)).hom = (λ_ G.X).inv ≫ MonObj.one ▷ G.X := by
    rw [BraidedCategory.braiding_naturality_right, ← Category.assoc]
    congr 1
    rw [Iso.inv_comp_eq, ← braiding_leftUnitor, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  calc (Mod.transpose v ≫ Mod.ihomRegularIso.hom.app H).hom
      = (ρ_ G.X).inv ≫ G.X ◁ MonObj.one ≫
          (Mod.transpose v ≫ Mod.ihomRegularIso.hom.app H).hom ▷ _ ≫ Mod.rightAct H := by
        rw [reassoc_of% e₁, hunit, Category.comp_id]
    _ = (ρ_ G.X).inv ≫ G.X ◁ MonObj.one ≫ (β_ G.X (adicConstantSheaf l Z)).hom ≫
          v.hom ▷ G.X ≫ Mod.evaluation G H := by
        rw [Mod.comp_hom', comp_whiskerRight, Category.assoc]
        erw [h₁]
        rfl
    _ = (λ_ G.X).inv ≫ (MonObj.one (X := adicConstantSheaf l Z) ≫ v.hom) ▷ G.X ≫
          Mod.evaluation G H := by
        rw [reassoc_of% e₂, comp_whiskerRight, Category.assoc]

/-- The map of stalks of the morphism `G ⟶ H` corresponding to `v : ℚ̄_ℓ ⟶ 𝓗om(G, H)` is the
evaluation pairing with the stalk of the section `v(1)`. -/
lemma map_transpose_comp_ihomRegularIso_hom_app_hom_apply
    (Φ : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l) ⥤ WeilCoefficients.{u} l)
    [Φ.LaxMonoidal] {G H : AdicSheaf l Z} (v : AdicSheaf.unit l Z ⟶ (AdicSheaf.ihom G).obj H)
    (x : Φ.obj G.X) :
    (Φ.map (Mod.transpose v ≫ Mod.ihomRegularIso.hom.app H).hom).hom x =
      Mod.evaluationPairing Φ G H
        ((ε Φ ≫ Φ.map (MonObj.one (X := adicConstantSheaf l Z) ≫ v.hom)).hom 1) x := by
  rw [transpose_comp_ihomRegularIso_hom_app_hom, Functor.map_comp, Functor.map_comp,
    ← left_unitality_inv, Category.assoc, Category.assoc, ← μ_natural_left_assoc,
    ← comp_whiskerRight_assoc]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  rfl

/-- The restriction to a point of the global section `v(1)` of `v : ℚ̄_ℓ ⟶ N`. -/
lemma globalSectionsToUpperStar_globalSectionOfModHom' {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ Z) {N : AdicSheaf l Z} (v : AdicSheaf.unit l Z ⟶ N) :
    ((globalSectionsToUpperStar _ t).app N.X).hom (globalSectionOfModHom v) =
      (ε (stalkFunctor l t) ≫
        (stalkFunctor l t).map (MonObj.one (X := adicConstantSheaf l Z) ≫ v.hom)).hom 1 := by
  have hε := NatTrans.IsMonoidal.unit (τ := globalSectionsToUpperStar (WeilCoefficients.{u} l) t)
  have n := (globalSectionsToUpperStar (WeilCoefficients.{u} l) t).naturality
    (MonObj.one (X := adicConstantSheaf l Z) ≫ v.hom)
  rw [globalSectionOfModHom, globalSectionOfHom, ← ModuleCat.comp_apply, Category.assoc]
  erw [n]
  rw [reassoc_of% hε]

end Uncurry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.UniversalCovers

open ProEtale FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  {U : Scheme.UniversalCovers Y Ω}
  (hU : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
    Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)))
  [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y]

/-- An element of the stalk of `M` killed by `φ : M ⟶ N` comes from the stalk of the kernel of
`φ`: the stalk functor is left exact. -/
lemma exists_stalkFunctor_map_kernel_ι_eq {K : Type u} [Field K] {Z : Scheme.{u}}
    (t : Spec (.of K) ⟶ Z) {M N : AdicSheaf l Z} (φ : M ⟶ N) (x : (stalkFunctor l t).obj M.X)
    (hx : ((stalkFunctor l t).map φ.hom).hom x = 0) :
    ∃ y, ((stalkFunctor l t).map (kernel.ι φ).hom).hom y = x := by
  let F := AdicSheaf.forget Z ⋙ stalkFunctor l t
  refine ⟨((PreservesKernel.iso F φ).inv).hom
    ((ModuleCat.kernelIsoKer (F.map φ)).inv.hom ⟨x, hx⟩), ?_⟩
  change ((PreservesKernel.iso F φ).inv ≫ F.map (kernel.ι φ)).hom _ = x
  rw [PreservesKernel.iso_inv_ι, ← ModuleCat.comp_apply, ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

omit [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] in
/-- **The stalk functor is faithful** on lisse sheaves on an irreducible scheme, e.g. a
connected normal locally Noetherian scheme. -/
theorem lisseStalk_faithful_of_irreducibleSpace [IrreducibleSpace Y]
    (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G H : LisseSheaf l Y} (f g : G ⟶ H)
    (h : (lisseStalk l t).map f = (lisseStalk l t).map g) : f = g := by
  let φ : G.obj ⟶ H.obj := f.hom - g.hom
  have hφ : (stalkFunctor l t).map φ.hom = 0 := by
    have e : (stalkFunctor l t).map φ.hom =
        (AdicSheaf.forget Y ⋙ stalkFunctor l t).map f.hom -
          (AdicSheaf.forget Y ⋙ stalkFunctor l t).map g.hom :=
      (AdicSheaf.forget Y ⋙ stalkFunctor l t).map_sub
    rw [e, sub_eq_zero]
    exact h
  have hK := (isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace G.property H.property φ).1
  have : Epi (kernel.ι φ) := hK.epi_of_surjective_stalkFunctor_map G.property _ t fun x ↦
    exists_stalkFunctor_map_kernel_ι_eq t φ x (by rw [hφ]; rfl)
  have h0 : φ = 0 := by
    rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]
  exact ObjectProperty.hom_ext _ (sub_eq_zero.1 h0)

omit [CompactSpace Y] in
/-- **The stalk functor is faithful** on lisse sheaves on a connected regular Noetherian
scheme, which is irreducible (`AlgebraicGeometry.IsRegular.irreducibleSpace`). -/
theorem lisseStalk_faithful (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G H : LisseSheaf l Y}
    (f g : G ⟶ H) (h : (lisseStalk l t).map f = (lisseStalk l t).map g) : f = g :=
  have := IsRegular.irreducibleSpace Y
  lisseStalk_faithful_of_irreducibleSpace t f g h

include hU in
omit [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] in
/-- The transport of stalks preserves the evaluation pairing `𝓗om(G, N)_y × G_y → N_y`. -/
lemma monoIso_evaluationPairing_general {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) (G N : LisseSheaf l Y)
    (hGN : IsAdicLisseSheaf ((AdicSheaf.ihom G.obj).obj N.obj))
    (d : (stalkFunctor l y).obj ((AdicSheaf.ihom G.obj).obj N.obj).X)
    (v : (stalkFunctor l y).obj G.obj.X) :
    Mod.evaluationPairing (stalkFunctor l z) G.obj N.obj
        (((monoIso hU τ).hom.app ⟨_, hGN⟩).hom d) (((monoIso hU τ).hom.app G).hom v) =
      ((monoIso hU τ).hom.app N).hom
        (Mod.evaluationPairing (stalkFunctor l y) G.obj N.obj d v) := by
  have hd := isIso_ptRes_app hU y ⟨_, hGN⟩
  have hv := isIso_ptRes_app hU y G
  obtain ⟨d, rfl⟩ : ∃ d₀, ((U.ptRes l y).app _).hom d₀ = d :=
    ⟨(inv ((U.ptRes l y).app _)).hom d, by rw [← ModuleCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
  obtain ⟨v, rfl⟩ : ∃ v₀, ((U.ptRes l y).app _).hom v₀ = v :=
    ⟨(inv ((U.ptRes l y).app _)).hom v, by rw [← ModuleCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rw [monoIso_hom_app_ptRes_apply hU τ ⟨_, hGN⟩, monoIso_hom_app_ptRes_apply hU τ G,
    evaluationPairing_natTrans, evaluationPairing_natTrans, evaluationPairing_natTrans]
  exact (monoIso_hom_app_ptRes_apply hU τ N _).symm

include hU in
omit [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] in
/-- **The stalk functor is full onto equivariant maps** (blueprint:
`proposition-lattices-representations-normal-scheme`). An equivariant map `φ : G_t → H_t` is an
invariant element of the stalk `𝓗om(G, H)_t = Hom(G_t, H_t)`, hence the restriction of a global
section of the lisse sheaf `𝓗om(G, H)`
(`AlgebraicGeometry.Scheme.UniversalCovers.exists_globalSection_of_invariant`),
that is, of a morphism `G ⟶ H`. -/
theorem lisseMonodromy_full (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G H : LisseSheaf l Y}
    (φ : LisseMonodromy.StalkSpace t G →ₗ[PadicAlgCl l] LisseMonodromy.StalkSpace t H)
    (hφ : ∀ g v, φ ((U.lisseMonodromy hU).rep t G g v) = (U.lisseMonodromy hU).rep t H g (φ v)) :
    ∃ f : G ⟶ H, ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom = φ := by
  have hGH : IsAdicLisseSheaf ((AdicSheaf.ihom G.obj).obj H.obj) := G.property.ihom H.property
  let Mh : LisseSheaf l Y := ⟨_, hGH⟩
  have hP := WeilCoefficients.bijective_homLinearMap
    (G.property.bijective_evaluationPairing_of_lisse H.obj t)
  obtain ⟨m, hm⟩ := hP.2 φ
  have hinv (g : Aut (fiber t)) : ((monoIso hU g.asIso).hom.app Mh).hom m = m := by
    refine hP.1 (LinearMap.ext fun x ↦ ?_)
    obtain ⟨w, rfl⟩ : ∃ w, ((monoIso hU g.asIso).hom.app G).hom w = x :=
      ⟨((monoIso hU g.asIso).inv.app G).hom x, by
        rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app]; rfl⟩
    rw [WeilCoefficients.homLinearMap_apply, WeilCoefficients.homLinearMap_apply,
      monoIso_evaluationPairing_general hU g.asIso G H hGH]
    have h₁ := LinearMap.congr_fun hm w
    have h₂ := LinearMap.congr_fun hm (((monoIso hU g.asIso).hom.app G).hom w)
    rw [WeilCoefficients.homLinearMap_apply] at h₁ h₂
    rw [h₁, h₂]
    exact (hφ g w).symm
  obtain ⟨σ, hσ⟩ := exists_globalSection_of_invariant hU t Mh m hinv
  obtain ⟨β, hβ⟩ := (bijective_globalSectionOfModHom Mh.obj).2 σ
  refine ⟨ObjectProperty.homMk (Mod.transpose β ≫ Mod.ihomRegularIso.hom.app H.obj),
    LinearMap.ext fun x ↦ ?_⟩
  change ((stalkFunctor l t).map (Mod.transpose β ≫ Mod.ihomRegularIso.hom.app H.obj).hom).hom x =
    φ x
  rw [map_transpose_comp_ihomRegularIso_hom_app_hom_apply,
    ← globalSectionsToUpperStar_globalSectionOfModHom', hβ, hσ]
  have h := LinearMap.congr_fun hm x
  rw [WeilCoefficients.homLinearMap_apply] at h
  exact h

include hU in
omit [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] in
/-- **Every continuous finite-dimensional representation is a monodromy representation**
(blueprint: `proposition-lattices-representations-normal-scheme`, essential surjectivity for
`Λ = ℚ̄_ℓ`). On a connected regular Noetherian scheme, every continuous finite-dimensional
`ℚ̄_ℓ`-representation `ρ` of `π₁(Y, t)` is isomorphic to the monodromy representation on the stalk
`G_t` of a lisse sheaf `G`.

This is the standard construction of the lisse sheaf attached to a representation
(SGA 4½, *Rapport*, 2.10; Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 7.4.7 and
Proposition 7.4.10): `π₁(Y, t)` being compact, `ρ` is defined over the ring of integers `𝒪_E`
of a finite extension `E` of `ℚ_ℓ` and preserves an `𝒪_E`-lattice `Λ ⊆ V`; the reductions
`Λ / ϖⁿ` are continuous representations of `π₁(Y, t)` on finite sets, hence finite étale covers
of `Y`, which define finite locally constant sheaves `L_n`, and `G = (lim_n L_n) ⊗_{𝒪_E} ℚ̄_ℓ`.
Here the lisse sheaf is instead obtained directly by descent of `ℚ̄_ℓⁿ` along the universal cover
`Ỹ_t ⟶ Y` for the loop cocycle of the matrix of `ρ`
(`AlgebraicGeometry.Scheme.UniversalCovers.exists_lisseSheaf_rep`). -/
theorem lisseMonodromy_essSurj (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (V : Type (u + 1)) [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) (Aut (fiber t)) V)
    (hρ : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ (G : LisseSheaf l Y) (e : LisseMonodromy.StalkSpace t G ≃ₗ[PadicAlgCl l] V),
      ∀ g v, e ((U.lisseMonodromy hU).rep t G g v) = ρ g (e v) :=
  exists_lisseSheaf_rep hU t V ρ hρ

omit [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] in
/-- **The monodromy from universal covers is an equivalence at every base point** (blueprint:
`proposition-lattices-representations-normal-scheme`, the case `Λ = ℚ̄_ℓ`), on an irreducible
scheme, e.g. a connected normal locally Noetherian scheme. -/
theorem lisseMonodromy_isEquivalenceAt_of_irreducibleSpace [IrreducibleSpace Y]
    (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : (U.lisseMonodromy hU).IsEquivalenceAt t where
  continuous_rep := lisseMonodromy_continuous_rep hU t
  faithful := lisseStalk_faithful_of_irreducibleSpace t
  full := lisseMonodromy_full hU t
  essSurj := lisseMonodromy_essSurj hU t

omit [CompactSpace Y] in
/-- **The monodromy from universal covers is an equivalence at every base point** (blueprint:
`proposition-lattices-representations-normal-scheme`, the case `Λ = ℚ̄_ℓ`), on a connected regular
Noetherian scheme, which is irreducible (`AlgebraicGeometry.IsRegular.irreducibleSpace`). -/
theorem lisseMonodromy_isEquivalenceAt (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    (U.lisseMonodromy hU).IsEquivalenceAt t :=
  have := IsRegular.irreducibleSpace Y
  lisseMonodromy_isEquivalenceAt_of_irreducibleSpace hU t

end AlgebraicGeometry.Scheme.UniversalCovers
