/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTowerSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeFrame
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntAbSheafPowLocal

/-!
# The tower of an integral cocycle is constant over the cover

Let `f : V ⟶ Y` be weakly étale and `γ` a continuous integral cocycle on `V ×_Y V`
(`AlgebraicGeometry.IsIntegralCocycle`). Over an object `U ⟶ V` of the small pro-étale site of
`V`, which factors through `f`, the twisted sections of the reductions of `γ` are the locally
constant functions `U → (ℤ_ℓ ⧸ ℓᵏ)ᴺ` (`AlgebraicGeometry.frameEval`,
`AlgebraicGeometry.frameExt`). Hence the restriction to `V` of the pro-étale tower of `γ` is the
constant tower `(ℤ/ℓᵏ)_V^N` (`AlgebraicGeometry.frameTowerIso`), compatibly with the reductions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Matrix

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.Functor

/-- The direct sum of copies of a functor, on morphisms, followed by a projection. -/
lemma biproductPow_map_π {K D : Type*} [Category K] [Category D] [Preadditive D]
    [HasFiniteBiproducts D] (F : K ⥤ D) (ι : Type*) [Finite ι] {k k' : K} (g : k ⟶ k')
    (i : ι) : (F.biproductPow ι).map g ≫ biproduct.π _ i = biproduct.π _ i ≫ F.map g :=
  biproduct.map_π (f := fun _ : ι ↦ F.obj k) (g := fun _ : ι ↦ F.obj k') (fun _ ↦ F.map g) i

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme ProEtale

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}} (f : V ⟶ Y) [hf : WeaklyEtale f] {N : ℕ}
  (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l])

/-- The restriction to `V` of the pro-étale tower of an integral cocycle, as abelian sheaves. -/
noncomputable abbrev frameTower : ℕᵒᵖ ⥤ Sheaf (ProEt.topology V) Ab.{u + 1} :=
  proEtIntegralCocycleTower γ ⋙
    sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab) ⋙
      ProEtale.localizationRestriction Ab.{u + 1} f hf

variable (l) in
/-- The additive identification `ℤ_ℓ ⧸ ℓᵏ ≃ ℤ/ℓᵏ`. -/
noncomputable abbrev towerEquiv (k : ℕ) :
    ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k ≃+ ZMod (l ^ k) :=
  ULift.padicIntQuotientSpanPowAddEquiv.{u + 1} l k

variable (l) in
/-- The identification `ℤ_ℓ ⧸ ℓᵏ ≃ ℤ/ℓᵏ` is compatible with the reductions. -/
lemma towerEquiv_towerFactor {k k' : ℕ} (h : k' ≤ k)
    (x : ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) :
    towerEquiv l k' (towerFactor.{u} l h x) =
      ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ k')) (towerEquiv l k x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have e₁ : towerFactor.{u} l h (Ideal.Quotient.mk _ a) = towerReduce l k' a.down := rfl
  have e₂ : (Ideal.Quotient.mk (towerIdeal.{u} l k) a) = towerReduce l k a.down := rfl
  rw [e₁, e₂, padicIntQuotientSpanPowAddEquiv_towerReduce,
    padicIntQuotientSpanPowAddEquiv_towerReduce, ZMod.castHom_apply, PadicInt.cast_toZModPow _ _ h]

section Maps

variable {f γ}

/-- The `i`-th coordinate, modulo `ℓᵏ`, of a twisted section over `U ⟶ V`, restricted along the
section of `V ×_Y U ⟶ U`. -/
noncomputable def frameCoord (k : ℕ) (i : Fin N) (U : V.ProEt)
    (σ : twistedSubmodule f (levelCocycleInt γ k) (U.hom ≫ f)) : ↥U.left → ZMod (l ^ k) :=
  fun u ↦ towerEquiv l k (frameEval f U.hom rfl σ.1 u i)

omit hf in
/-- The coordinates of a twisted section are locally constant. -/
lemma isLocallyConstant_frameCoord (k : ℕ) (i : Fin N) (U : V.ProEt)
    (σ : twistedSubmodule f (levelCocycleInt γ k) (U.hom ≫ f)) :
    IsLocallyConstant (frameCoord k i U σ) :=
  (((mem_twistedSubmodule f _).1 σ.2).1.comp_continuous
    (frameSection f U.hom rfl).base.hom.continuous).comp fun v ↦ towerEquiv l k (v i)

/-- The `i`-th coordinate of the restriction to `V` of the pro-étale tower, modulo `ℓᵏ`. -/
noncomputable def frameEvalHom (k : ℕ) (i : Fin N) :
    (frameTower f γ).obj (op k) ⟶ (zmodPowAbSheafDiagram V l).obj (op k) :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    { app U := AddCommGrpCat.ofHom
        { toFun σ := ULift.up ⟨frameCoord k i U.unop σ,
            (isLocallyConstant_frameCoord k i U.unop σ).continuous⟩
          map_zero' := ULift.ext (ContinuousMap.ext fun _ ↦ map_zero (towerEquiv l k))
          map_add' σ τ := ULift.ext (ContinuousMap.ext fun _ ↦ map_add (towerEquiv l k) _ _) }
      naturality U U' g := by
        ext σ
        refine ULift.ext (ContinuousMap.ext fun u ↦ ?_)
        have := congrFun (frameEval_comp_eq (f := f) U.unop.hom rfl g.unop.left
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (MorphismProperty.Over.w g.unop)))
          (a' := U'.unop.hom) rfl (MorphismProperty.Over.w g.unop) σ.1) u
        exact congrArg (fun v ↦ towerEquiv l k (v i)) this }

lemma frameEvalHom_hom_app_apply (k : ℕ) (i : Fin N) (U : V.ProEtᵒᵖ)
    (σ : twistedSubmodule f (levelCocycleInt γ k) (U.unop.hom ≫ f)) :
    ((frameEvalHom k i).hom.app U σ).down = ⟨frameCoord k i U.unop σ,
      (isLocallyConstant_frameCoord k i U.unop σ).continuous⟩ :=
  rfl

variable (hγ : IsIntegralCocycle f γ)

/-- The twisted section `(v, u) ↦ γ(v, u) eᵢ x(u)` extending `x eᵢ`, for a function `x` on
`U ⟶ V` with values in `ℤ/ℓᵏ`. -/
noncomputable def frameExtSection (k : ℕ) (i : Fin N) (U : V.ProEt)
    (x : C(U.left, ZMod (l ^ k))) :
    twistedSubmodule f (levelCocycleInt γ k) (U.hom ≫ f) :=
  ⟨frameExt f U.hom rfl (fun z ↦ levelCocycleInt γ k z)
      (fun u ↦ Pi.single i ((towerEquiv l k).symm (x u))),
    (mem_twistedSubmodule f _).2 (isTwistedSection_frameExt U.hom rfl
      (hγ.isDescentCocycle_int k) (((IsLocallyConstant.iff_continuous x).2 x.continuous).comp
        fun a : ZMod (l ^ k) ↦ (Pi.single i ((towerEquiv l k).symm a) : LevelModule.{u} l N k)))⟩

omit hf in
/-- The underlying function of `AlgebraicGeometry.frameExtSection`. -/
lemma frameExtSection_coe (k : ℕ) (i : Fin N) (U : V.ProEt) (x : C(U.left, ZMod (l ^ k))) :
    (frameExtSection hγ k i U x : ↥(pullback f (U.hom ≫ f)) → LevelModule.{u} l N k) =
      frameExt f U.hom rfl (fun z ↦ levelCocycleInt γ k z)
        (fun u ↦ Pi.single i ((towerEquiv l k).symm (x u))) :=
  rfl

/-- The extension of the `i`-th coordinate functions modulo `ℓᵏ` to twisted sections. -/
noncomputable def frameExtHom (hγ : IsIntegralCocycle f γ) (k : ℕ) (i : Fin N) :
    (zmodPowAbSheafDiagram V l).obj (op k) ⟶ (frameTower f γ).obj (op k) :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    { app U := AddCommGrpCat.ofHom
        { toFun x := frameExtSection hγ k i U.unop x.down
          map_zero' := Subtype.ext (by
            rw [frameExtSection_coe, Submodule.coe_zero,
              ← frameExt_zero U.unop.hom rfl (levelCocycleInt γ k)]
            congr 1
            funext u
            simp)
          map_add' x y := Subtype.ext (by
            rw [Submodule.coe_add, frameExtSection_coe, frameExtSection_coe, frameExtSection_coe,
              ← frameExt_add]
            congr 1
            funext u
            rw [Pi.add_apply, ← Pi.single_add, ← map_add]
            rfl) }
      naturality U U' g := by
        ext x
        refine Subtype.ext ?_
        exact frameExt_comp_eq (f := f) U.unop.hom rfl g.unop.left
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (MorphismProperty.Over.w g.unop)))
          (a' := U'.unop.hom) rfl (MorphismProperty.Over.w g.unop)
          (c := fun z ↦ levelCocycleInt γ k z)
          (fun u ↦ (Pi.single i ((towerEquiv l k).symm (x.down u)) : LevelModule.{u} l N k)) }

/-- The extension of coordinate functions, on sections. -/
lemma frameExtHom_hom_app_apply (k : ℕ) (i : Fin N) (U : V.ProEtᵒᵖ)
    (x : ULift.{u + 1} C(U.unop.left, ZMod (l ^ k))) :
    (frameExtHom hγ k i).hom.app U x = frameExtSection hγ k i U.unop x.down :=
  rfl

/-- The `j`-th coordinate of the extension of the `i`-th coordinate function is `δᵢⱼ` times it. -/
lemma frameEvalHom_frameExtHom (k : ℕ) (i j : Fin N) :
    frameExtHom hγ k i ≫ frameEvalHom k j = if i = j then 𝟙 _ else 0 := by
  ext U x
  refine ULift.ext (ContinuousMap.ext fun u ↦ ?_)
  have h := congrFun (frameEval_frameExt (f := f) U.unop.hom rfl (hγ.isDescentCocycle_int k)
    (fun u ↦ (Pi.single i ((towerEquiv l k).symm (x.down u)) : LevelModule.{u} l N k))) u
  change towerEquiv l k (frameEval f U.unop.hom rfl (frameExt f U.unop.hom rfl
    (fun z ↦ levelCocycleInt γ k z)
    (fun u ↦ (Pi.single i ((towerEquiv l k).symm (x.down u)) : LevelModule.{u} l N k))) u j) = _
  rw [h]
  split_ifs with hij
  · subst hij
    simp only [Pi.single_eq_same, AddEquiv.apply_symm_apply]
    rfl
  · rw [Pi.single_eq_of_ne (Ne.symm hij), map_zero]
    rfl

/-- Morphisms into the restricted tower are determined by their coordinates. -/
lemma frameEvalHom_ext {k : ℕ} {Z : Sheaf (ProEt.topology V) Ab.{u + 1}}
    {g g' : Z ⟶ (frameTower f γ).obj (op k)}
    (H : ∀ i, g ≫ frameEvalHom k i = g' ≫ frameEvalHom k i) : g = g' := by
  ext U s
  have hσ := (mem_twistedSubmodule f _).1 (g.hom.app U s).2
  have hσ' := (mem_twistedSubmodule f _).1 (g'.hom.app U s).2
  refine Subtype.ext ?_
  rw [← frameExt_frameEval U.unop.hom rfl hσ, ← frameExt_frameEval U.unop.hom rfl hσ']
  congr 1
  funext u i
  have := congrArg (fun φ : Z ⟶ (zmodPowAbSheafDiagram V l).obj (op k) ↦
    ((φ.hom.app U s).down u)) (H i)
  exact (towerEquiv l k).injective this

/-- The coordinates and the extensions of coordinate functions exhibit the restricted tower as a
direct sum. -/
lemma sum_frameEvalHom_frameExtHom (k : ℕ) :
    ∑ i, frameEvalHom k i ≫ frameExtHom hγ k i = 𝟙 ((frameTower f γ).obj (op k)) := by
  refine frameEvalHom_ext fun j ↦ ?_
  simp only [Preadditive.sum_comp, Category.assoc, frameEvalHom_frameExtHom, Category.id_comp]
  rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [ite_eq_right hb, comp_zero]) (by simp),
    ite_eq_left rfl,
    Category.comp_id]

/-- The restriction to `V` of the pro-étale tower, at level `k`, as a direct sum of copies of
the constant sheaf `(ℤ/ℓᵏ)_V`. -/
noncomputable def frameBicone (hγ : IsIntegralCocycle f γ) (k : ℕ) :
    Bicone fun _ : Fin N ↦ (zmodPowAbSheafDiagram V l).obj (op k) where
  pt := (frameTower f γ).obj (op k)
  π i := frameEvalHom k i
  ι i := frameExtHom hγ k i
  ι_π i j := by
    rw [frameEvalHom_frameExtHom]
    split_ifs <;> rfl

/-- **The restriction to `V` of the pro-étale tower is constant**, at each level. -/
noncomputable def frameTowerObjIso (hγ : IsIntegralCocycle f γ) (k : ℕ) :
    (frameTower f γ).obj (op k) ≅ (zmodPowAbSheafDiagramPow V l N).obj (op k) :=
  biproduct.uniqueUpToIso _ (isBilimitOfTotal (frameBicone hγ k)
    (sum_frameEvalHom_frameExtHom hγ k))

/-- The isomorphism `AlgebraicGeometry.frameTowerObjIso`, followed by a projection, is a
coordinate. -/
lemma frameTowerObjIso_hom_π (k : ℕ) (i : Fin N) :
    (frameTowerObjIso hγ k).hom ≫ biproduct.π _ i = frameEvalHom k i := by
  rw [frameTowerObjIso, biproduct.uniqueUpToIso_hom, biproduct.lift_π]
  rfl

/-- The coordinates are compatible with the reductions. -/
lemma frameEvalHom_naturality {k k' : ℕ} (h : k' ≤ k) (i : Fin N) :
    (frameTower f γ).map (homOfLE h).op ≫ frameEvalHom k' i =
      frameEvalHom k i ≫ (zmodPowAbSheafDiagram V l).map (homOfLE h).op := by
  ext U σ
  refine ULift.ext (ContinuousMap.ext fun u ↦ ?_)
  exact towerEquiv_towerFactor l h _

/-- **The restriction to `V` of the pro-étale tower is the constant tower `(ℤ/ℓᵏ)_V^N`.** -/
noncomputable def frameTowerIso (hγ : IsIntegralCocycle f γ) :
    frameTower f γ ≅ zmodPowAbSheafDiagramPow V l N :=
  NatIso.ofComponents (fun k ↦ frameTowerObjIso hγ k.unop) fun {k k'} h ↦ by
    refine biproduct.hom_ext _ _ fun j ↦ ?_
    rw [Category.assoc, frameTowerObjIso_hom_π, Category.assoc]
    rw [Functor.biproductPow_map_π]
    rw [← Category.assoc, frameTowerObjIso_hom_π]
    exact frameEvalHom_naturality (leOfHom h.unop) j

/-- **The limit of the restriction to `V` of the pro-étale tower is `ℤ_ℓ,V^N`.** -/
noncomputable def frameLimitIso (hγ : IsIntegralCocycle f γ) :
    limit (frameTower f γ) ≅ ⨁ fun _ : Fin N ↦ padicIntAbSheaf V l :=
  lim.mapIso (frameTowerIso hγ) ≪≫ limitZmodPowAbSheafDiagramPowIso V l N

end Maps

end AlgebraicGeometry
