/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Sections of the coefficient rings over weakly contractible objects

Let `X` be a scheme with a morphism `k : X ⟶ Spec ℤ` and `Λ` a condensed abelian group. The
coefficient sheaf `Λ_X = k^* p^* Λ` on `X_proét` is the sheafified left Kan extension of `Λ` along
the profinite test objects `S ↦ X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X`. This functor has a left
adjoint `π₀ : X_proét ⥤ Profinite`, `V ↦ π₀(Spec Γ(V, ⊤))`
(`AlgebraicGeometry.ProEtale.connectedComponentsAlongAdjunction`): maps `V ⟶ X[S]` over `X` are
ring maps `LC(S, ℤ) ⟶ Γ(V, ⊤)`, i.e. continuous maps `π₀(Spec Γ(V, ⊤)) ⟶ S`. Hence the left Kan
extension is `V ↦ Λ(π₀ V)`, and `Λ_X` is its sheafification
(`AlgebraicGeometry.ProEtale.connectedComponentsAlongSheafIso`).

Over an object `U` whose covering sieves contain finite decompositions into disjoint open
subschemes, e.g. `U = Spec R` with `R` w-contractible, the sheafification does not change the
sections
(`ProEtale.bijective_toSheafify_connectedComponentsAlong_of_forall_exists_retraction`).
So the sections of `Λ_X` over `U` are `Λ(π₀ U)`: the map `Λ(π₀ U) ⟶ Λ_X(X[π₀ U]) ⟶ Λ_X(U)`
given by the unit of `p_X^* ⊣ p_{X*}` and the restriction along the unit `U ⟶ X[π₀ U]` is bijective
(`AlgebraicGeometry.ProEtale.bijective_unit_app_comp_map_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### Connected components of spectra -/

section ConnectedComponents

/-- The continuous map `Spec R ⟶ S` induced by a ring map `LC(S, ℤ) ⟶ R`. -/
noncomputable def spectrumProjection {S : Profinite.{u}} {R : Type u} [CommRing R]
    (φ : LocallyConstant S ℤ →+* R) : C(PrimeSpectrum R, S) :=
  ⟨fun p ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (PrimeSpectrum.comap φ p)).1,
    continuous_fst.comp
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous.comp
        (PrimeSpectrum.continuous_comap φ))⟩

lemma localization_map_eq_eval_spectrumProjection {S : Profinite.{u}} {R : Type u} [CommRing R]
    (φ : LocallyConstant S ℤ →+* R) (p : PrimeSpectrum R) (g : LocallyConstant S ℤ) :
    algebraMap R (Localization.AtPrime p.asIdeal) (φ g) =
      algebraMap R (Localization.AtPrime p.asIdeal) (g (spectrumProjection φ p) : R) := by
  classical
  let s := spectrumProjection φ p
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

/-- Ring maps `LC(S, ℤ) ⟶ R` are continuous maps `π₀(Spec R) ⟶ S`: a ring map `R' ⟶ LC(S, ℤ)` in
`CommRingCatᵒᵖ` is a continuous map from the space of connected components of `Spec R` to `S`. -/
noncomputable def connectedComponentsHomEquiv (R : CommRingCat.{u}ᵒᵖ) (S : Profinite.{u}) :
    (Profinite.of (ConnectedComponents (PrimeSpectrum R.unop)) ⟶ S) ≃
      (R ⟶ profiniteToCommRingCatOp.obj S) where
  toFun f := (CommRingCat.ofHom (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R.unop)
    ⟨fun p ↦ f (ConnectedComponents.mk p), f.hom.hom.continuous.comp
      ConnectedComponents.continuous_coe⟩)).op
  invFun φ := ConcreteCategory.ofHom
    ⟨(spectrumProjection φ.unop.hom).continuous.connectedComponentsLift,
      (spectrumProjection φ.unop.hom).continuous.connectedComponentsLift_continuous⟩
  left_inv f := by
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe x
    change (spectrumProjection (LocallyConstant.liftPrimeSpectrum (Int.castRingHom R.unop)
      ⟨fun p ↦ f (ConnectedComponents.mk p), f.hom.hom.continuous.comp
        ConnectedComponents.continuous_coe⟩)) p = f (ConnectedComponents.mk p)
    dsimp [spectrumProjection]
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
          (spectrumProjection φ.unop.hom) g) = _
    rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
    exact (localization_map_eq_eval_spectrumProjection φ.unop.hom p g).symm

lemma connectedComponentsHomEquiv_naturality (R : CommRingCat.{u}ᵒᵖ)
    (S T : Profinite.{u}) (g : S ⟶ T)
    (f : Profinite.of (ConnectedComponents (PrimeSpectrum R.unop)) ⟶ S) :
    connectedComponentsHomEquiv R T (f ≫ g) =
      connectedComponentsHomEquiv R S f ≫ profiniteToCommRingCatOp.map g := by
  apply Quiver.Hom.unop_inj
  ext (h : LocallyConstant T ℤ)
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

/-- The functor `R ↦ π₀(Spec R)` from rings to profinite sets, left adjoint to
`S ↦ LC(S, ℤ)` (`AlgebraicGeometry.ProEtale.connectedComponentsAdjunction`). -/
noncomputable def connectedComponentsFunctor : CommRingCat.{u}ᵒᵖ ⥤ Profinite.{u} :=
  Adjunction.leftAdjointOfEquiv connectedComponentsHomEquiv
    connectedComponentsHomEquiv_naturality

/-- The adjunction `π₀ ∘ Spec ⊣ LC(-, ℤ)` between rings and profinite sets. -/
noncomputable def connectedComponentsAdjunction :
    connectedComponentsFunctor.{u} ⊣ profiniteToCommRingCatOp :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The adjunction `π₀ ∘ Spec ∘ Γ ⊣ (S ↦ Spec LC(S, ℤ))` between schemes and profinite sets:
morphisms `V ⟶ Spec LC(S, ℤ)` are continuous maps `π₀(Spec Γ(V, ⊤)) ⟶ S`. -/
noncomputable def schemeConnectedComponentsAdjunction :
    Scheme.Γ.rightOp ⋙ connectedComponentsFunctor.{u} ⊣ profiniteToScheme :=
  ΓSpec.adjunction.comp connectedComponentsAdjunction

end ConnectedComponents

/-! ### The profinite test objects along a structure morphism -/

section Along

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u})

/-- The profinite test objects `S ↦ X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X` of the small pro-étale site
of `X`, for a structure morphism `k : X ⟶ Spec ℤ`. -/
noncomputable abbrev profiniteToProEtAlong : Profinite.{u} ⥤ X.ProEt :=
  profiniteToProEt ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ k

/-- Morphisms `V ⟶ X[S]` over `X` are morphisms of schemes `V ⟶ Spec LC(S, ℤ)`. -/
noncomputable def homProfiniteToProEtAlongEquiv (V : X.ProEt) (S : Profinite.{u}) :
    (V ⟶ (profiniteToProEtAlong k).obj S) ≃ (V.left ⟶ profiniteToScheme.obj S) where
  toFun g := g.left ≫ pullback.fst _ _
  invFun h := MorphismProperty.Over.homMk
    (pullback.lift h V.hom (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _)
  left_inv g := MorphismProperty.Over.Hom.ext (pullback.hom_ext (by simp)
    (by simpa using (MorphismProperty.Over.w g).symm))
  right_inv h := pullback.lift_fst _ _ _

lemma homProfiniteToProEtAlongEquiv_naturality (V : X.ProEt) {S S' : Profinite.{u}}
    (g : V ⟶ (profiniteToProEtAlong k).obj S) (φ : S ⟶ S') :
    homProfiniteToProEtAlongEquiv k V S' (g ≫ (profiniteToProEtAlong k).map φ) =
      homProfiniteToProEtAlongEquiv k V S g ≫ profiniteToScheme.map φ := by
  simp only [homProfiniteToProEtAlongEquiv, Equiv.coe_fn_mk]
  refine (Category.assoc _ _ _).trans ?_
  simp [profiniteToProEt]

/-- Morphisms `V ⟶ X[S]` over `X` are continuous maps `π₀(Spec Γ(V, ⊤)) ⟶ S`. -/
noncomputable def connectedComponentsAlongHomEquiv (V : X.ProEt) (S : Profinite.{u}) :
    ((Scheme.Γ.rightOp ⋙ connectedComponentsFunctor).obj V.left ⟶ S) ≃
      (V ⟶ (profiniteToProEtAlong k).obj S) :=
  (schemeConnectedComponentsAdjunction.homEquiv V.left S).trans
    (homProfiniteToProEtAlongEquiv k V S).symm

lemma connectedComponentsAlongHomEquiv_naturality (V : X.ProEt) (S S' : Profinite.{u})
    (φ : S ⟶ S') (g : (Scheme.Γ.rightOp ⋙ connectedComponentsFunctor).obj V.left ⟶ S) :
    connectedComponentsAlongHomEquiv k V S' (g ≫ φ) =
      connectedComponentsAlongHomEquiv k V S g ≫ (profiniteToProEtAlong k).map φ := by
  simp only [connectedComponentsAlongHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, Equiv.symm_apply_eq,
    homProfiniteToProEtAlongEquiv_naturality, Equiv.apply_symm_apply]

/-- The functor `V ↦ π₀(Spec Γ(V, ⊤))` from the small pro-étale site of `X` to profinite sets,
left adjoint to the profinite test objects `S ↦ X[S]`
(`AlgebraicGeometry.ProEtale.connectedComponentsAlongAdjunction`). -/
noncomputable def connectedComponentsAlong : X.ProEt ⥤ Profinite.{u} :=
  Adjunction.leftAdjointOfEquiv (connectedComponentsAlongHomEquiv k)
    (connectedComponentsAlongHomEquiv_naturality k)

/-- The adjunction `π₀ ⊣ (S ↦ X[S])` between the small pro-étale site of `X` and profinite sets. -/
noncomputable def connectedComponentsAlongAdjunction :
    connectedComponentsAlong k ⊣ profiniteToProEtAlong k :=
  Adjunction.adjunctionOfEquivLeft (connectedComponentsAlongHomEquiv k)
    (connectedComponentsAlongHomEquiv_naturality k)

lemma connectedComponentsAlongAdjunction_homEquiv (V : X.ProEt) (S : Profinite.{u})
    (f : (connectedComponentsAlong k).obj V ⟶ S) :
    (connectedComponentsAlongAdjunction k).homEquiv V S f =
      connectedComponentsAlongHomEquiv k V S f := by
  rw [connectedComponentsAlongAdjunction, Adjunction.adjunctionOfEquivLeft,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

lemma homProfiniteToProEtAlongEquiv_homEquiv (V : X.ProEt) (S : Profinite.{u})
    (f : (connectedComponentsAlong k).obj V ⟶ S) :
    homProfiniteToProEtAlongEquiv k V S ((connectedComponentsAlongAdjunction k).homEquiv V S f) =
      schemeConnectedComponentsAdjunction.homEquiv V.left S f := by
  rw [connectedComponentsAlongAdjunction_homEquiv, connectedComponentsAlongHomEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply]

end Along

/-! ### The coefficient sheaf as a sheafified precomposition with `π₀` -/

section Sheaf

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u})

/-- The functor sending a condensed abelian group `Λ` to the sheafification of the presheaf
`V ↦ Λ(π₀(Spec Γ(V, ⊤)))` on the small pro-étale site of `X`. -/
noncomputable def connectedComponentsAlongSheaf :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (connectedComponentsAlong k).op ⋙
    presheafToSheaf _ _

instance isContinuous_profiniteToProEtAlong :
    (profiniteToProEtAlong k).IsContinuous (coherentTopology Profinite.{u}) (ProEt.topology X) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ profiniteToProEt
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ k) _ (ProEt.topology specZ) _ _
    (Scheme.ProEt.isContinuous_overPullback k)

/-- The sheafified precomposition with `π₀` is left adjoint to the pushforward along the
profinite test objects, as `π₀` is left adjoint to `S ↦ X[S]`. -/
noncomputable def connectedComponentsAlongSheafAdjunction :
    connectedComponentsAlongSheaf k ⊣ (profiniteToProEtAlong k).sheafPushforwardContinuous
      Ab.{u + 1} (coherentTopology Profinite.{u}) (ProEt.topology X) :=
  (((connectedComponentsAlongAdjunction k).op.whiskerLeft Ab.{u + 1}).comp
    (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

lemma connectedComponentsAlongSheafAdjunction_unit_app_hom_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (S : Profinite.{u}) :
    ((connectedComponentsAlongSheafAdjunction k).unit.app Λ).hom.app (op S) =
      Λ.obj.map ((connectedComponentsAlongAdjunction k).counit.app S).op ≫
        (toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app
          (op ((profiniteToProEtAlong k).obj S)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (((connectedComponentsAlongAdjunction k).op.whiskerLeft Ab.{u + 1}).comp
      (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}))
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (L := connectedComponentsAlongSheaf k)
    (R := (profiniteToProEtAlong k).sheafPushforwardContinuous
      Ab.{u + 1} (coherentTopology Profinite.{u}) (ProEt.topology X)) (Iso.refl _) (Iso.refl _) Λ
  have h' := congrArg (fun φ ↦ φ.app (op S)) h
  simp only [Adjunction.comp_unit_app] at h'
  exact h'.trans (by simp)

/-- The adjunction `p_X^* ⊣ p_{X*}` along a structure morphism `k : X ⟶ Spec ℤ`, the composition of
`p^* ⊣ p_*` and `k^* ⊣ k_*`. The sections of `p_{X*} G` over `S` are the sections of `G` over
`X[S]`. -/
noncomputable def upperStarFromPointAlongAdjunction :
    pointUpperStar ⋙ (k)^*[Ab.{u + 1}] ⊣ (profiniteToProEtAlong k).sheafPushforwardContinuous
      Ab.{u + 1} (coherentTopology Profinite.{u}) (ProEt.topology X) :=
  pointUpperStarLowerStarAdjunction.comp (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} k)

/-- The coefficient sheaf `k^* p^* Λ` is the sheafification of `V ↦ Λ(π₀(Spec Γ(V, ⊤)))`, both
functors being left adjoint to the pushforward along the profinite test objects. -/
noncomputable def connectedComponentsAlongSheafIso :
    connectedComponentsAlongSheaf k ≅ pointUpperStar ⋙ (k)^*[Ab.{u + 1}] :=
  (connectedComponentsAlongSheafAdjunction k).leftAdjointUniq
    (upperStarFromPointAlongAdjunction k)

/-- The unit `Λ(π₀ V) ⟶ Λ_X(X[π₀ V])` of `p_X^* ⊣ p_{X*}` followed by the restriction along the unit
`V ⟶ X[π₀ V]` is the map to the sheafification of `V ↦ Λ(π₀ V)`, followed by the comparison
isomorphism `AlgebraicGeometry.ProEtale.connectedComponentsAlongSheafIso`. -/
lemma unit_app_comp_map_unit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (V : X.ProEt) :
    ((upperStarFromPointAlongAdjunction k).unit.app Λ).hom.app
        (op ((connectedComponentsAlong k).obj V)) ≫
      ((pointUpperStar ⋙ (k)^*[Ab.{u + 1}]).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction k).unit.app V).op =
    (toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app (op V) ≫
      ((connectedComponentsAlongSheafIso k).hom.app Λ).hom.app (op V) := by
  have h := (connectedComponentsAlongSheafAdjunction k).homEquiv_leftAdjointUniq_hom_app
    (upperStarFromPointAlongAdjunction k) Λ
  rw [Adjunction.homEquiv_unit] at h
  rw [← h]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [connectedComponentsAlongSheafAdjunction_unit_app_hom_app]
  have nθ := ((connectedComponentsAlongSheafIso k).hom.app Λ).hom.naturality
    ((connectedComponentsAlongAdjunction k).unit.app V).op
  have e1 : (toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app
        (op ((profiniteToProEtAlong k).obj ((connectedComponentsAlong k).obj V))) ≫
      ((connectedComponentsAlongSheaf k).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction k).unit.app V).op =
      ((connectedComponentsAlong k).op ⋙ Λ.obj).map
        ((connectedComponentsAlongAdjunction k).unit.app V).op ≫
      (toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app (op V) :=
    ((toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).naturality
      ((connectedComponentsAlongAdjunction k).unit.app V).op).symm
  have e2 : Λ.obj.map ((connectedComponentsAlongAdjunction k).counit.app
        ((connectedComponentsAlong k).obj V)).op ≫
      ((connectedComponentsAlong k).op ⋙ Λ.obj).map
        ((connectedComponentsAlongAdjunction k).unit.app V).op = 𝟙 _ := by
    rw [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, ← Functor.map_comp, ← op_comp,
      (connectedComponentsAlongAdjunction k).left_triangle_components V]
    exact Λ.obj.map_id _
  simp only [Category.assoc]
  erw [← nθ]
  calc _ = Λ.obj.map ((connectedComponentsAlongAdjunction k).counit.app
        ((connectedComponentsAlong k).obj V)).op ≫
      ((toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app
        (op ((profiniteToProEtAlong k).obj ((connectedComponentsAlong k).obj V))) ≫
      ((connectedComponentsAlongSheaf k).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction k).unit.app V).op) ≫
      ((connectedComponentsAlongSheafIso k).hom.app Λ).hom.app (op V) := by
        simp only [Category.assoc]
        rfl
    _ = _ := by rw [e1, ← Category.assoc, ← Category.assoc, e2, Category.id_comp]

/-- **Sections of the coefficient sheaf.** If the map from `V ↦ Λ(π₀ V)` to its sheafification is
bijective on sections over `V`, then the unit `Λ(π₀ V) ⟶ Λ_X(X[π₀ V])` followed by the restriction
along the unit `V ⟶ X[π₀ V]` is bijective: the sections of `Λ_X = k^* p^* Λ` over `V` are
`Λ(π₀ V)`. -/
theorem bijective_unit_app_comp_map_unit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (V : X.ProEt)
    (hV : Function.Bijective
      ((toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app (op V))) :
    Function.Bijective (((upperStarFromPointAlongAdjunction k).unit.app Λ).hom.app
        (op ((connectedComponentsAlong k).obj V)) ≫
      ((pointUpperStar ⋙ (k)^*[Ab.{u + 1}]).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction k).unit.app V).op) := by
  rw [unit_app_comp_map_unit, ConcreteCategory.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).comp hV

end Sheaf

/-! ### Sheafification over objects with disjoint open decompositions -/

section Sheafify

variable {X : Scheme.{u}}

/-- Let `U` be an object of `X_proét` such that every covering sieve contains a covering family
`Y i ⟶ U` for which the restriction `P(U) ⟶ ∏ P(Y i)` is bijective. Then the map from `P` to its
sheafification is bijective on sections over `U`. -/
lemma bijective_toSheafify_app_of_forall_exists (P : X.ProEtᵒᵖ ⥤ Ab.{u + 1}) {U : X.ProEt}
    (hU : ∀ S ∈ ProEt.topology X U, ∃ (ι : Type u) (Y : ι → X.ProEt) (f : ∀ i, Y i ⟶ U),
      Sieve.ofArrows Y f ∈ ProEt.topology X U ∧ (∀ i, S (f i)) ∧
        Function.Bijective (fun (x : P.obj (op U)) (i : ι) ↦ P.map (f i).op x)) :
    Function.Bijective ((toSheafify (ProEt.topology X) P).app (op U)) := by
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · obtain ⟨ι, Y, f, -, hS, hbij⟩ := hU _
      (Presheaf.equalizerSieve_mem (ProEt.topology X) (toSheafify _ P) x y hxy)
    exact hbij.1 (funext fun i ↦ hS i)
  · obtain ⟨ι, Y, f, hcov, hS, hbij⟩ := hU _
      (Presheaf.imageSieve_mem (ProEt.topology X) (toSheafify _ P) s)
    choose t ht using hS
    obtain ⟨x, hx⟩ := hbij.2 t
    refine ⟨x, ?_⟩
    have key (i : ι) : (sheafify (ProEt.topology X) P).map (f i).op
        ((toSheafify (ProEt.topology X) P).app (op U) x) =
          (sheafify (ProEt.topology X) P).map (f i).op s := by
      have hxi : P.map (f i).op x = t i := congrFun hx i
      rw [← NatTrans.naturality_apply, hxi, ht i]
    apply Sheaf.isSeparated ((presheafToSheaf (ProEt.topology X) Ab.{u + 1}).obj P) _ _ hcov
    rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, key i]

/-- Pairwise disjoint opens covering an object `U` of `X_proét` exhibit `U` as their coproduct. -/
noncomputable def isColimitCofanOfDisjointOpens (U : X.ProEt) {ι : Type u}
    (O : ι → U.left.Opens) (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hcov : ∀ x, ∃ i, x ∈ O i) :
    IsColimit (Cofan.mk U fun i ↦ ProEt.ofOpenImmersionHom U (O i).ι) := by
  have h := (nonempty_isColimit_cofanMk_of (fun i ↦ (O i).ι)
    (by
      rw [eq_top_iff]
      intro x _
      obtain ⟨i, hi⟩ := hcov x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa using hi⟩)
    (fun i j hij ↦ by simpa using hdisj i j hij)).some
  refine Cofan.IsColimit.mk _ (fun t ↦ MorphismProperty.Over.homMk
      (Cofan.IsColimit.desc h fun i ↦ (t.inj i).left) ?_) (fun t i ↦ ?_) (fun t m hm ↦ ?_)
  · refine Cofan.IsColimit.hom_ext h _ _ fun i ↦ ?_
    rw [← Category.assoc, Cofan.IsColimit.fac h]
    exact (MorphismProperty.Over.w (t.inj i)).trans rfl
  · exact MorphismProperty.Over.Hom.ext (Cofan.IsColimit.fac h _ i)
  · refine MorphismProperty.Over.Hom.ext (Cofan.IsColimit.hom_ext h _ _ fun i ↦ ?_)
    exact (congrArg (fun m ↦ m.left) (hm i)).trans
      (Cofan.IsColimit.fac h (fun i ↦ (t.inj i).left) i).symm

/-- For a limit fan of abelian groups, the map from the cone point to the product of the
underlying sets is bijective. -/
lemma bijective_of_isLimit_fan {ι : Type u} {F : ι → Ab.{u + 1}} {P : Ab.{u + 1}}
    (g : ∀ i, P ⟶ F i) (h : IsLimit (Fan.mk P g)) :
    Function.Bijective (fun (x : P) (i : ι) ↦ g i x) := by
  have hT := (Types.isLimit_iff _).1 ⟨isLimitOfPreserves (CategoryTheory.forget Ab.{u + 1}) h⟩
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · obtain ⟨z, -, hz⟩ := hT (fun j ↦ g j.as x) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨h⟩⟩; cases h; simp)
    exact (hz x fun _ ↦ rfl).trans (hz y fun j ↦ (congrFun hxy j.as).symm).symm
  · obtain ⟨z, hz, -⟩ := hT (fun j ↦ s j.as) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨h⟩⟩; cases h; simp)
    exact ⟨z, funext fun i ↦ hz ⟨i⟩⟩

/-- Let `U` be an object of `X_proét` with `U.left ≅ Spec R`, where every faithfully flat
ind-étale `R`-algebra has a retraction (e.g. `R` is w-contractible). Then the map from the presheaf
`V ↦ Λ(π₀ V)` to its sheafification is bijective on sections over `U`: every covering sieve of `U`
contains a decomposition of `U` into finitely many disjoint open subschemes, which is a coproduct
decomposition preserved by the left adjoint `π₀`, and `Λ` turns finite coproducts into
products. -/
theorem bijective_toSheafify_connectedComponentsAlong_of_forall_exists_retraction
    (k : X ⟶ specZ.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) {U : X.ProEt}
    {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : U.left ≅ Spec R) :
    Function.Bijective
      ((toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app (op U)) := by
  refine bijective_toSheafify_app_of_forall_exists _ fun S hS ↦ ?_
  obtain ⟨κ, O, hdisj, hcov, hSO⟩ :=
    ProEt.exists_disjoint_opens_of_forall_exists_retraction hR e hS
  -- Only finitely many of the disjoint opens are nonempty, `U` being quasi-compact.
  have : IsAffine U.left := .of_isIso e.hom
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i ↦ (O i : Set U.left))
    (fun i ↦ (O i).isOpen) (fun x _ ↦ Set.mem_iUnion.2 (hcov x))
  let κ' := {i : κ // (O i : Set U.left).Nonempty}
  have hmem (i : κ') : i.1 ∈ t := by
    obtain ⟨x, hx⟩ := i.2
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    by_cases hij : i.1 = j
    · rwa [hij]
    · exact absurd ((disjoint_iff.1 (hdisj i.1 j hij)).le ⟨hx, hxj⟩) (by simp)
  have : Finite κ' := Finite.of_injective (fun i : κ' ↦ (⟨i.1, hmem i⟩ : t))
    fun i j hij ↦ Subtype.ext (by simpa using congrArg Subtype.val hij)
  have : Fintype κ' := Fintype.ofFinite _
  have hcov' (x : U.left) : ∃ i : κ', x ∈ O i.1 := by
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨⟨i, x, hi⟩, hi⟩
  refine ⟨κ', fun i ↦ ProEt.ofOpenImmersion U (O i.1).ι,
    fun i ↦ ProEt.ofOpenImmersionHom U (O i.1).ι, ?_, fun i ↦ hSO i.1, ?_⟩
  · refine ProEt.mem_topology_of_openImmersion _ (fun i : κ' ↦ (O i.1).ι) (fun x ↦ ?_)
      (fun i ↦ Sieve.ofArrows_mk _ _ i)
    obtain ⟨i, hi⟩ := hcov' x
    exact ⟨i, by simpa using hi⟩
  · have hcol := isColimitCofanOfDisjointOpens U (fun i : κ' ↦ O i.1)
      (fun i j hij ↦ hdisj _ _ fun h ↦ hij (Subtype.ext h)) hcov'
    have := (connectedComponentsAlongAdjunction k).leftAdjoint_preservesColimits
    have hT := (isColimitMapCoconeCofanMkEquiv (connectedComponentsAlong k) _ _).1
      (isColimitOfPreserves (connectedComponentsAlong k) hcol)
    have hL := (isLimitMapConeFanMkEquiv Λ.obj _ _).1
      (isLimitOfPreserves Λ.obj (Cofan.IsColimit.op hT))
    exact bijective_of_isLimit_fan _ hL

end Sheafify

end AlgebraicGeometry.ProEtale
