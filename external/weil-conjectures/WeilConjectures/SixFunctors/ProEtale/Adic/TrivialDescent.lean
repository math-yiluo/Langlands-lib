/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection

/-!
# Descent of trivial `ℓ`-adic sheaves along pro-étale covers

Let `f : W ⟶ X` be weakly étale, surjective and quasi-compact, and `γ` a cocycle of matrices of
locally finite functions on `W ×_X W`. The sheaf `G` on `X` whose sections over `T` are the
columns `y` of locally finite functions on `T ×_X W` with `γ(w₁, w₂) y(t, w₁) = y(t, w₂)` is the
kernel of a morphism `f_* ℚ̄_ℓⁿ ⟶ (p₁ f)_* ℚ̄_ℓⁿ`. The adjoint `f^* G ⟶ ℚ̄_ℓⁿ` of the inclusion
is an isomorphism, computed on sections through the identification of `f^*` with restriction
along the localization functor: a section `y` restricts along the graph of `T ⟶ W` to
`y(t, a t)`, and conversely `c ↦ γ(a t, w) c(t)`. Its transition matrix is `γ`, by the kernel
condition, the composites of adjunctions computing the pullbacks of the trivialisation
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_iso_transitionMatrix_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

namespace AdicSheaf

section Components

variable {B : Scheme.{u}} {n : ℕ}

/-- The pullback of a function on `B` to an object `Z` of the pro-étale site of `B`. -/
noncomputable abbrev pullFun (Z : B.ProEt) (a : PadicAlgCl.locallyFiniteFunctions l B) :
    PadicAlgCl.locallyFiniteFunctions l Z.left :=
  PadicAlgCl.locallyFiniteFunctionsComp l Z.hom.base.hom a

/-- The components of a section of `ℚ̄_ℓ,Bⁿ` over `Z`: a column of locally finite functions. -/
noncomputable def comps {Z : B.ProEt} (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    Fin n → PadicAlgCl.locallyFiniteFunctions l Z.left :=
  fun i ↦ ((biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) x).down

/-- The sections of a sheaf of modules over `Z`, as an additive functor. -/
noncomputable abbrev sectionsFunctor (Z : B.ProEt) : AdicSheaf l B ⥤ WeilCoefficients.{u} l :=
  AdicSheaf.forget B ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op Z)

/-- The sections functor on morphisms. -/
lemma sectionsFunctor_map_apply {Z : B.ProEt} {M N : AdicSheaf l B} (φ : M ⟶ N)
    (x : M.X.obj.obj (op Z)) : ((sectionsFunctor Z).map φ).hom x = φ.hom.hom.app (op Z) x :=
  rfl

/-- A section of `ℚ̄_ℓ,Bⁿ` is the sum of its components. -/
lemma eq_sum_comps {Z : B.ProEt} (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    x = ∑ i, (biproduct.ι (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z)
      ((biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) x) := by
  have e := congrArg (fun φ ↦ ((sectionsFunctor (l := l) Z).map φ).hom x)
    (biproduct.total (f := fun _ : Fin n ↦ unit l B))
  simp only [CategoryTheory.Functor.map_id, Functor.map_sum, ModuleCat.hom_sum,
    LinearMap.sum_apply, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e.symm

/-- Sections of `ℚ̄_ℓ,Bⁿ` are determined by their components. -/
lemma comps_injective {Z : B.ProEt} :
    Function.Injective (comps (l := l) (B := B) (n := n) (Z := Z)) := by
  intro x x' h
  rw [eq_sum_comps x, eq_sum_comps x']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact ULift.ext (congrFun h i)

/-- The section of `ℚ̄_ℓ,Bⁿ` over `Z` with given components. -/
noncomputable def ofComps {Z : B.ProEt} (c : Fin n → PadicAlgCl.locallyFiniteFunctions l Z.left) :
    (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z) :=
  ∑ i, (biproduct.ι (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) (ULift.up (c i))

/-- The components of the section with given components. -/
lemma comps_ofComps {Z : B.ProEt}
    (c : Fin n → PadicAlgCl.locallyFiniteFunctions l Z.left) :
    comps (ofComps (l := l) (B := B) c) = c := by
  classical
  funext j
  simp only [comps, ofComps, ← sectionsFunctor_map_apply, map_sum, ← ModuleCat.comp_apply,
    ← Functor.map_comp]
  rw [Finset.sum_eq_single j]
  · rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id]
    rfl
  · intro i _ hij
    rw [biproduct.ι_π_ne _ hij, Functor.map_zero]
    rfl
  · simp

/-- Every column of functions is the components of a section. -/
lemma comps_surjective {Z : B.ProEt} :
    Function.Surjective (comps (l := l) (B := B) (n := n) (Z := Z)) :=
  fun c ↦ ⟨ofComps c, comps_ofComps c⟩

/-- The components of the restriction of a section are the pulled back components. -/
lemma comps_map {Z Z' : B.ProEt} (k : Z' ⟶ Z)
    (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    comps ((⨁ fun _ : Fin n ↦ unit l B).X.obj.map k.op x) =
      fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l k.left.base.hom (comps x i) := by
  funext i
  have e := NatTrans.naturality_apply (biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom k.op x
  simp only [comps]
  erw [e]
  rfl

/-- The components of the image of a section under a morphism of free modules. -/
lemma comps_app {Z : B.ProEt} (ψ : (⨁ fun _ : Fin n ↦ unit l B) ⟶ ⨁ fun _ : Fin n ↦ unit l B)
    (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    comps (ψ.hom.hom.app (op Z) x) = fun i ↦ ∑ j,
      pullFun Z (unitMatrix ψ i j) * comps x j := by
  funext i
  conv_lhs => rw [eq_sum_comps x]
  simp only [comps, map_sum]
  rw [show ∀ (g : Fin n → ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l Z.left)),
    (∑ j, g j).down = ∑ j, (g j).down from fun g ↦ map_sum AddEquiv.ulift g _]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have e : (biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z) (ψ.hom.hom.app (op Z)
      ((biproduct.ι (fun _ : Fin n ↦ unit l B) j).hom.hom.app (op Z)
        ((biproduct.π (fun _ : Fin n ↦ unit l B) j).hom.hom.app (op Z) x))) =
      (biproduct.ι (fun _ : Fin n ↦ unit l B) j ≫ ψ ≫
        biproduct.π (fun _ : Fin n ↦ unit l B) i).hom.hom.app (op Z)
          ((biproduct.π (fun _ : Fin n ↦ unit l B) j).hom.hom.app (op Z) x) := rfl
  erw [e, adicConstantSheaf_app_eq_mul _ (unit_hom_linear _), adicConstantSheaf_app_one]
  rw [mul_comm]
  rfl

end Components

section Pull

variable {W P : Scheme.{u}} (a : P ⟶ W) {n : ℕ}

/-- Pulling back functions along `a : P ⟶ W`, as a morphism of modules
`ℚ̄_ℓ,W ⟶ a_* ℚ̄_ℓ,P`. -/
noncomputable def toLowerStarUnit : unit l W ⟶ (a)_*ᵃ[l].obj (unit l P) :=
  (adicUpperStarLowerStarAdjunction l a).unit.app (unit l W) ≫
    (a)_*ᵃ[l].map (adicUpperStarUnitIso l a).hom

/-- Pulling back functions along `a`, on underlying sheaves. -/
lemma toLowerStarUnit_hom :
    (toLowerStarUnit (l := l) a).hom = adicConstantSheafToLowerStar l a := by
  rw [toLowerStarUnit, Mod.comp_hom', adicLowerStar_map_hom, adicUpperStarLowerStarAdjunction,
    Adjunction.modAdjunction_unit_app_hom]
  simp only [adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  exact ((upperStarLowerStarAdjunction _ a).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- Pulling back columns of functions along `a : P ⟶ W`, as a morphism
`ℚ̄_ℓ,Wⁿ ⟶ a_* ℚ̄_ℓ,Pⁿ`: the adjoint of `a^* ℚ̄_ℓ,Wⁿ ≅ ℚ̄_ℓ,Pⁿ`. -/
noncomputable def freePull :
    (⨁ fun _ : Fin n ↦ unit l W) ⟶ (a)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l P) :=
  (adicUpperStarLowerStarAdjunction l a).unit.app _ ≫
    (a)_*ᵃ[l].map (freeUpperStarIso l (Fin n) a).hom

/-- Pulling back columns of functions is the adjoint of `a^* ℚ̄_ℓ,Wⁿ ≅ ℚ̄_ℓ,Pⁿ`. -/
lemma freePull_eq : freePull (l := l) (n := n) a =
    (adicUpperStarLowerStarAdjunction l a).homEquiv _ _ (freeUpperStarIso l (Fin n) a).hom :=
  ((adicUpperStarLowerStarAdjunction l a).homEquiv_unit _ _ _).symm

/-- Pulling back columns of functions, componentwise. -/
lemma freePull_π (i : Fin n) :
    freePull (l := l) a ≫ (a)_*ᵃ[l].map (biproduct.π (fun _ : Fin n ↦ unit l P) i) =
      biproduct.π (fun _ : Fin n ↦ unit l W) i ≫ toLowerStarUnit a := by
  rw [freePull, Category.assoc, ← Functor.map_comp, freeUpperStarIso_hom_π, Functor.map_comp]
  have := (adicUpperStarLowerStarAdjunction l a).unit.naturality
    (biproduct.π (fun _ : Fin n ↦ unit l W) i)
  simp only [Functor.comp_map, Functor.id_map] at this
  rw [← Category.assoc]
  erw [← this]
  rw [Category.assoc]
  rfl

/-- **Pulling back columns of functions**, on sections. -/
lemma comps_freePull {Z : W.ProEt} (x : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj (op Z)) :
    comps (B := P) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj Z)
      ((freePull (l := l) a).hom.hom.app (op Z) x) = fun i ↦
        PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst Z.hom a).base.hom (comps x i) := by
  funext i
  change ((freePull a ≫ (a)_*ᵃ[l].map (biproduct.π (fun _ : Fin n ↦ unit l P) i)).hom.hom.app
    (op Z) x).down = _
  rw [freePull_π, Mod.comp_hom', ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, toLowerStarUnit_hom]
  rfl

end Pull

section DescentMap

variable {X W : Scheme.{u}} (f : W ⟶ X) {n : ℕ}
  (γ : Matrix (Fin n) (Fin n) (PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback f f)))

/-- The first half of the descent map, `y ↦ γ · p₁^* y`. -/
noncomputable def descentMapFst :
    (f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l W) ⟶
      (pullback.fst f f ≫ f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) :=
  (f)_*ᵃ[l].map (freePull (pullback.fst f f) ≫ (pullback.fst f f)_*ᵃ[l].map (ofUnitMatrix γ)) ≫
      (adicLowerStarComp l (pullback.fst f f) f).hom.app
        (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f))

/-- The second half of the descent map, `y ↦ p₂^* y`. -/
noncomputable def descentMapSnd :
    (f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l W) ⟶
      (pullback.fst f f ≫ f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) :=
  (f)_*ᵃ[l].map (freePull (pullback.snd f f)) ≫
      (adicLowerStarComp l (pullback.snd f f) f).hom.app
        (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) ≫
        (adicLowerStarCongr l pullback.condition.symm).hom.app
          (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f))

/-- The morphism `f_* ℚ̄_ℓ,Wⁿ ⟶ (p₁ f)_* ℚ̄_ℓ,(W ×_X W)ⁿ`, `y ↦ γ · p₁^* y - p₂^* y`, whose
kernel is the descent of `ℚ̄_ℓ,Wⁿ` along `γ`. -/
noncomputable def descentMap :
    (f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l W) ⟶
      (pullback.fst f f ≫ f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) :=
  descentMapFst f γ - descentMapSnd f

/-- The descent map is the difference of its two halves. -/
lemma descentMap_eq : descentMap (l := l) f γ = descentMapFst f γ - descentMapSnd f := by
  -- Compare section maps without unfolding the full composite sheaf morphisms.
  apply Mod.hom_ext
  ext T x
  rfl

/-- The map `T ×_X (W ×_X W) ⟶ T ×_X W` induced by the first projection. -/
noncomputable abbrev descentρ₁ (T : X.ProEt) :
    Limits.pullback T.hom (pullback.fst f f ≫ f) ⟶ Limits.pullback T.hom f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst f f)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The map `T ×_X (W ×_X W) ⟶ T ×_X W` induced by the second projection. -/
noncomputable abbrev descentρ₂ (T : X.ProEt) :
    Limits.pullback T.hom (pullback.fst f f ≫ f) ⟶ Limits.pullback T.hom f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd f f)
    (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition)

/-- The components of the zero section. -/
lemma comps_zero {B : Scheme.{u}} {Z : B.ProEt} :
    comps (0 : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) = 0 := by
  funext i
  simp only [comps, map_zero]
  rfl

/-- The components of a difference of sections. -/
lemma comps_sub {B : Scheme.{u}} {Z : B.ProEt}
    (x x' : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj (op Z)) :
    comps (x - x') = comps x - comps x' := by
  funext i
  simp only [comps, map_sub, Pi.sub_apply]
  rfl

/-- The restriction along the composition isomorphism of base changes. -/
lemma pullbackComp_hom_app_left_comp_fst {Y : Scheme.{u}} (a : Y ⟶ W) (T : X.ProEt) :
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) a f).hom.app T).left ≫
      pullback.fst (pullback.snd T.hom f) a =
        pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a)
          (by rw [pullback.condition, Category.assoc]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, MorphismProperty.Over.pullbackComp_left_fst_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, pullback.lift_snd, ← Category.assoc]
    congr 1
    exact MorphismProperty.Over.w ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
      (Q := ⊤) a f).hom.app T)

/-- Sections of a composite of morphisms. -/
lemma comp_hom_app_apply {B : Scheme.{u}} {M N K : AdicSheaf l B} (φ : M ⟶ N) (ψ : N ⟶ K)
    (U : B.ProEtᵒᵖ) (x : M.X.obj.obj U) :
    (φ ≫ ψ).hom.hom.app U x = ψ.hom.hom.app U (φ.hom.hom.app U x) :=
  rfl

/-- The composition isomorphism of pushforwards on sections. -/
lemma adicLowerStarComp_hom_app_apply {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (M : AdicSheaf l T) (V : R.ProEtᵒᵖ) (x : ((h₁)_*ᵃ[l].obj M |> (h₂)_*ᵃ[l].obj).X.obj.obj V) :
    ((adicLowerStarComp l h₁ h₂).hom.app M).hom.hom.app V x =
      M.X.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop).op x := by
  rw [adicLowerStarComp_hom_app_hom, lowerStarComp_hom_app_hom_app]
  rfl

/-- The pushforward of a morphism on sections. -/
lemma adicLowerStar_map_hom_app_apply {S T : Scheme.{u}} (h : T ⟶ S) {M N : AdicSheaf l T}
    (φ : M ⟶ N) (V : S.ProEtᵒᵖ) (x : ((h)_*ᵃ[l].obj M).X.obj.obj V) :
    ((h)_*ᵃ[l].map φ).hom.hom.app V x =
      φ.hom.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj V.unop)) x :=
  rfl

/-- Sections of a difference of morphisms. -/
lemma hom_app_sub {B : Scheme.{u}} {M N : AdicSheaf l B} (φ ψ : M ⟶ N) (U : B.ProEtᵒᵖ)
    (x : M.X.obj.obj U) : (φ - ψ).hom.hom.app U x = φ.hom.hom.app U x - ψ.hom.hom.app U x := by
  change ((sectionsFunctor (l := l) U.unop).map (φ - ψ)).hom x = _
  rw [Functor.map_sub]
  rfl

/-- The first half of the descent map on sections. -/
lemma comps_descentMap_fst (T : X.ProEt)
    (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T))) :
    comps (B := Limits.pullback f f)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.fst f f ≫ f)).obj T)
      ((descentMapFst (l := l) f γ).hom.hom.app (op T) y) = fun i ↦
        ∑ j, PadicAlgCl.locallyFiniteFunctionsComp l
          (pullback.snd T.hom (pullback.fst f f ≫ f)).base.hom (γ i j) *
          PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₁ f T).base.hom (comps y j) := by
  delta descentMapFst
  erw [Mod.comp_hom', ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  erw [adicLowerStarComp_hom_app_hom, lowerStarComp_hom_app_hom_app, comps_map]
  erw [adicLowerStar_map_hom, lowerStar_map_hom_app', Mod.comp_hom',
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    adicLowerStar_map_hom, lowerStar_map_hom_app', comps_app, comps_freePull,
    unitMatrix_ofUnitMatrix]
  funext i
  have h₁ := MorphismProperty.Over.w ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale)
    (Q := ⊤) (pullback.fst f f) f).hom.app T)
  have h₂ := pullbackComp_hom_app_left_comp_fst f (pullback.fst f f) T
  refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  simp only [PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply,
    AddSubmonoidClass.coe_finsetSum, ContinuousMap.sum_apply, MulMemClass.coe_mul,
    ContinuousMap.mul_apply, pullFun]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 2
  · exact congrArg (fun φ ↦ φ.base x) h₁
  · exact congrArg (fun φ ↦ φ.base x) h₂

omit [Fact l.Prime] in
/-- The identification `g_* ≅ g'_*` for `g = g'`, on sections of free modules. -/
lemma comps_adicLowerStarCongr {B : Scheme.{u}} [Fact l.Prime] {g g' : B ⟶ X} (h : g = g')
    (T : X.ProEt) (x : (⨁ fun _ : Fin n ↦ unit l B).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj T))) :
    comps (B := B) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g').obj T)
      (((adicLowerStarCongr l h).hom.app (⨁ fun _ : Fin n ↦ unit l B)).hom.hom.app (op T) x) =
        fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l
          (pullback.lift (pullback.fst T.hom g') (pullback.snd T.hom g')
            (by rw [pullback.condition, h])).base.hom (comps x i) := by
  subst h
  have e : pullback.lift (pullback.fst T.hom g) (pullback.snd T.hom g) pullback.condition =
      𝟙 _ := pullback.hom_ext (by simp) (by simp)
  rw [e]
  rfl

/-- The second half of the descent map on sections. -/
lemma comps_descentMap_snd (T : X.ProEt)
    (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T))) :
    comps (B := Limits.pullback f f)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.fst f f ≫ f)).obj T)
      (((f)_*ᵃ[l].map (freePull (pullback.snd f f)) ≫
        (adicLowerStarComp l (pullback.snd f f) f).hom.app (⨁ fun _ : Fin n ↦
          unit l (Limits.pullback f f)) ≫
          (adicLowerStarCongr l pullback.condition.symm).hom.app _).hom.hom.app (op T) y) =
        fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₂ f T).base.hom (comps y i) := by
  rw [comp_hom_app_apply, comp_hom_app_apply, adicLowerStar_map_hom_app_apply]
  rw [comps_adicLowerStarCongr]
  generalize hz : (freePull (l := l) (n := n) (pullback.snd f f)).hom.hom.app
    (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T)) y = z
  erw [adicLowerStarComp_hom_app_apply (l := l) (pullback.snd f f) f
    (⨁ fun _ : Fin n ↦ unit l (Limits.pullback f f)) (op T) z]
  rw [comps_map, ← hz, comps_freePull]
  funext i
  have h₁ := pullbackComp_hom_app_left_comp_fst f (pullback.snd f f) T
  have key : pullback.lift (pullback.fst T.hom (pullback.fst f f ≫ f))
      (pullback.snd T.hom (pullback.fst f f ≫ f))
        (pullback.condition.trans (congrArg (pullback.snd T.hom (pullback.fst f f ≫ f) ≫ ·)
          pullback.condition)) ≫
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        (pullback.snd f f) f).hom.app T).left ≫
      pullback.fst (pullback.snd T.hom f) (pullback.snd f f) = descentρ₂ f T := by
    rw [h₁]
    exact pullback.hom_ext (by simp) (by simp)
  refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  simp only [PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply]
  exact congrArg (fun φ ↦ (comps y i).1 (φ.base x)) key

/-- **The descent map on sections**: `y ↦ γ · p₁^* y - p₂^* y`. -/
lemma comps_descentMap (T : X.ProEt)
    (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T))) :
    comps (B := Limits.pullback f f)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (pullback.fst f f ≫ f)).obj T)
      ((descentMap (l := l) f γ).hom.hom.app (op T) y) = fun i ↦
        (∑ j, PadicAlgCl.locallyFiniteFunctionsComp l
          (pullback.snd T.hom (pullback.fst f f ≫ f)).base.hom (γ i j) *
          PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₁ f T).base.hom (comps y j)) -
        PadicAlgCl.locallyFiniteFunctionsComp l (descentρ₂ f T).base.hom (comps y i) := by
  rw [descentMap, hom_app_sub, comps_sub, comps_descentMap_fst]
  have e : descentMapSnd (l := l) (n := n) f = (f)_*ᵃ[l].map (freePull (pullback.snd f f)) ≫
      (adicLowerStarComp l (pullback.snd f f) f).hom.app (⨁ fun _ : Fin n ↦
        unit l (Limits.pullback f f)) ≫
        (adicLowerStarCongr l pullback.condition.symm).hom.app _ := rfl
  rw [e, comps_descentMap_snd]
  rfl

end DescentMap

section Localization

variable {V U : Scheme.{u}} (g : V ⟶ U) (hg : WeaklyEtale g)

/-- The counit of `j_g^* ⊣ g_*` restricts sections along the graph `T ⟶ T ×_U V`. -/
lemma localizationRestrictionLowerStarAdjunction_counit_app_hom_app
    (N : Sheaf (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)) (T : V.ProEt) :
    ((ProEtale.localizationRestrictionLowerStarAdjunction _ g hg).counit.app N).hom.app (op T) =
      N.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g hg
        trivial).unit.app T).op := by
  simp [ProEtale.localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous]

end Localization

section Kernel

variable {B : Scheme.{u}} {M N : AdicSheaf l B} (φ : M ⟶ N) (U : B.ProEt)

/-- The sections functor is left exact. -/
instance : PreservesFiniteLimits (sectionsFunctor (l := l) U) := by
  unfold sectionsFunctor
  infer_instance

/-- The inclusion of a kernel is injective on sections. -/
lemma kernel_ι_injective : Function.Injective ((kernel.ι φ).hom.hom.app (op U)) := by
  have : Mono ((sectionsFunctor (l := l) U).map (kernel.ι φ)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

/-- The sections killed by a morphism come from the kernel. -/
lemma exists_kernel_ι_eq (y : M.X.obj.obj (op U)) (hy : φ.hom.hom.app (op U) y = 0) :
    ∃ s, (kernel.ι φ).hom.hom.app (op U) s = y := by
  let F := sectionsFunctor (l := l) U
  refine ⟨((PreservesKernel.iso F φ).inv).hom
    ((ModuleCat.kernelIsoKer (F.map φ)).inv.hom ⟨y, hy⟩), ?_⟩
  change ((PreservesKernel.iso F φ).inv ≫ F.map (kernel.ι φ)).hom _ = y
  rw [PreservesKernel.iso_inv_ι, ← ModuleCat.comp_apply, ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

/-- The sections of a kernel map to zero. -/
lemma kernel_ι_app_comp (s : (kernel φ).X.obj.obj (op U)) :
    φ.hom.hom.app (op U) ((kernel.ι φ).hom.hom.app (op U) s) = 0 := by
  rw [← comp_hom_app_apply, kernel.condition]
  rfl

end Kernel

section Descent

variable {X W : Scheme.{u}} (f : W ⟶ X) [WeaklyEtale f] {n : ℕ}
  (γ : Matrix (Fin n) (Fin n) (PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback f f)))

/-- The descent of `ℚ̄_ℓ,Wⁿ` along the cocycle `γ`: the kernel of the descent map. -/
noncomputable def descentSheaf : AdicSheaf l X :=
  kernel (descentMap (l := l) f γ)

/-- The comparison `f^* G ⟶ ℚ̄_ℓ,Wⁿ`, adjoint to the inclusion `G ⟶ f_* ℚ̄_ℓ,Wⁿ`. -/
noncomputable def descentTriv :
    (f)^*ᵃ[l].obj (descentSheaf f γ) ⟶ ⨁ fun _ : Fin n ↦ unit l W :=
  ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _).symm (kernel.ι (descentMap (l := l) f γ))

/-- The comparison `f^* G ⟶ ℚ̄_ℓ,Wⁿ`, through the identification of `f^*` with restriction along
the localization functor. -/
lemma descentTriv_hom : (descentTriv f γ).hom =
    (ProEtale.upperStarIsoLocalizationRestriction _ f inferInstance).hom.app _ ≫
      (ProEtale.localizationRestriction _ f inferInstance).map
        (kernel.ι (descentMap (l := l) f γ)).hom ≫
      (ProEtale.localizationRestrictionLowerStarAdjunction _ f inferInstance).counit.app
        (⨁ fun _ : Fin n ↦ unit l W).X := by
  rw [descentTriv, adicUpperStarLowerStarAdjunction]
  erw [Adjunction.modAdjunction_homEquiv_symm_apply_hom]
  rw [Adjunction.homEquiv_counit, ← Adjunction.leftAdjointUniq_hom_app_counit
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f)
      (ProEtale.localizationRestrictionLowerStarAdjunction _ f inferInstance)]
  have nat := (ProEtale.upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) f
    inferInstance).hom.naturality (kernel.ι (descentMap (l := l) f γ)).hom
  have := nat =≫ (ProEtale.localizationRestrictionLowerStarAdjunction _ f
    inferInstance).counit.app (⨁ fun _ : Fin n ↦ unit l W).X
  simp only [Category.assoc] at this
  exact this

/-- The comparison on sections over `T ∈ W_proét`: restriction of `y ∈ G(T ⟶ X)` along the
graph `T ⟶ T ×_X W`. -/
noncomputable abbrev descentTrivApp (T : W.ProEt) :
    (descentSheaf (l := l) f γ).X.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).obj T)) →
      (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj (op T) :=
  fun s ↦ (⨁ fun _ : Fin n ↦ unit l W).X.obj.map ((MorphismProperty.Over.mapPullbackAdj
    @WeaklyEtale ⊤ f inferInstance trivial).unit.app T).op
      ((kernel.ι (descentMap (l := l) f γ)).hom.hom.app _ s)

variable {f γ} in
/-- **The comparison is bijective on sections**: a section `y` of `G` over `T ⟶ X` satisfies
`y(t, w) = γ(a t, w) y(t, a t)`, so it is determined by its restriction `c(t) = y(t, a t)` to the
graph, and conversely `c ↦ γ(a t, w) c(t)` is a section of `G` by the cocycle condition. -/
lemma bijective_descentTrivApp
    (hdiag : γ.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) = 1)
    (hcoc : γ.map (PadicAlgCl.locallyFiniteFunctionsComp l (tripleProj₁₃ f).base.hom) =
      γ.map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.snd (pullback.snd f f) (pullback.fst f f)).base.hom) *
      γ.map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.fst (pullback.snd f f) (pullback.fst f f)).base.hom)) (T : W.ProEt) :
    Function.Bijective (descentTrivApp (l := l) f γ T) := by
  classical
  set T' := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).obj T
  set u := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f inferInstance trivial).unit.app T
  have hu₁ : u.left ≫ pullback.fst T'.hom f = 𝟙 _ := pullback.lift_fst _ _ _
  have hu₂ : u.left ≫ pullback.snd T'.hom f = T.hom := pullback.lift_snd _ _ _
  have hT' : T'.hom = T.hom ≫ f := rfl
  let ψ : Limits.pullback T'.hom f ⟶ Limits.pullback f f :=
    pullback.lift (pullback.fst _ _ ≫ T.hom) (pullback.snd _ _)
      (by rw [Category.assoc, ← hT', pullback.condition])
  let σ : Limits.pullback T'.hom f ⟶ Limits.pullback T'.hom (pullback.fst f f ≫ f) :=
    pullback.lift (pullback.fst _ _) ψ (by simp [ψ, T'])
  have hσ₁ : σ ≫ descentρ₁ f T' = pullback.fst _ _ ≫ u.left := by
    refine pullback.hom_ext ?_ ?_
    · simp only [σ, Category.assoc, pullback.lift_fst]
      rw [hu₁]
      exact (Category.comp_id _).symm
    · simp only [σ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hu₂]
      exact pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ descentρ₂ f T' = 𝟙 _ := pullback.hom_ext (by simp [σ]) (by simp [σ, ψ])
  have hσ₃ : σ ≫ pullback.snd _ _ = ψ := pullback.lift_snd _ _ _
  have hpt₁ (x) : (descentρ₁ f T').base (σ.base x) =
      u.left.base ((pullback.fst T'.hom f).base x) := by
    rw [← Scheme.Hom.comp_apply, hσ₁, Scheme.Hom.comp_apply]
    rfl
  have hpt₂ (x) : (descentρ₂ f T').base (σ.base x) = x := by
    rw [← Scheme.Hom.comp_apply, hσ₂]
    rfl
  have hpt₃ (x) : (pullback.snd T'.hom (pullback.fst f f ≫ f)).base (σ.base x) = ψ.base x := by
    rw [← Scheme.Hom.comp_apply, hσ₃]
  -- the relation satisfied by the sections of the kernel
  have hrel (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T')))
      (hy : (descentMap (l := l) f γ).hom.hom.app (op T') y = 0) (i : Fin n) (x) :
      (comps y i).1 x = ∑ j, (γ i j).1 (ψ.base x) *
        (comps y j).1 (u.left.base ((pullback.fst T'.hom f).base x)) := by
    have h := congrArg (fun c ↦ (c i).1 (σ.base x)) (comps_descentMap (l := l) f γ T' y)
    simp only [hy, comps_zero, Pi.zero_apply, ZeroMemClass.coe_zero, ContinuousMap.zero_apply,
      AddSubgroupClass.coe_sub, ContinuousMap.sub_apply, AddSubmonoidClass.coe_finsetSum,
      ContinuousMap.sum_apply, MulMemClass.coe_mul, ContinuousMap.mul_apply,
      PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply] at h
    erw [hpt₁ x, hpt₂ x, hpt₃ x] at h
    exact (sub_eq_zero.1 h.symm).symm
  have hmap (y : (⨁ fun _ : Fin n ↦ unit l W).X.obj.obj
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T'))) (j : Fin n) (z) :
      (comps ((⨁ fun _ : Fin n ↦ unit l W).X.obj.map u.op y) j).1 z =
        (comps y j).1 (u.left.base z) := by
    rw [comps_map]
    rfl
  constructor
  · intro s s' h
    rw [← sub_eq_zero]
    apply kernel_ι_injective (descentMap (l := l) f γ) T'
    rw [map_sub, map_zero]
    have hy : (descentMap (l := l) f γ).hom.hom.app (op T')
        ((kernel.ι (descentMap (l := l) f γ)).hom.hom.app (op T') s -
          (kernel.ι (descentMap (l := l) f γ)).hom.hom.app (op T') s') = 0 := by
      rw [map_sub, kernel_ι_app_comp, kernel_ι_app_comp, sub_zero]
    have hz : (⨁ fun _ : Fin n ↦ unit l W).X.obj.map u.op
        ((kernel.ι (descentMap (l := l) f γ)).hom.hom.app (op T') s -
          (kernel.ι (descentMap (l := l) f γ)).hom.hom.app (op T') s') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
    apply comps_injective
    rw [comps_zero]
    funext i
    refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
    rw [hrel _ hy i x]
    refine (Finset.sum_eq_zero fun j _ ↦ ?_).trans rfl
    rw [← hmap, hz, comps_zero]
    simp
  · intro z
    let c := comps z
    let yc : Fin n → PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback T'.hom f) := fun i ↦
      ∑ j, PadicAlgCl.locallyFiniteFunctionsComp l ψ.base.hom (γ i j) *
        PadicAlgCl.locallyFiniteFunctionsComp l (pullback.fst T'.hom f).base.hom (c j)
    let y := ofComps (l := l) (B := W)
      (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T') yc
    -- the triple point `(a t, w₁, w₂)`
    let Θ : Limits.pullback T'.hom (pullback.fst f f ≫ f) ⟶ tripleProduct f :=
      pullback.lift (descentρ₁ f T' ≫ ψ) (pullback.snd _ _) (by simp [ψ])
    have hΘ₁₂ : Θ ≫ pullback.fst _ _ = descentρ₁ f T' ≫ ψ := pullback.lift_fst _ _ _
    have hΘ₂₃ : Θ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have hΘ₁₃ : Θ ≫ tripleProj₁₃ f = descentρ₂ f T' ≫ ψ :=
      pullback.hom_ext (by simp [Θ, ψ]) (by simp [Θ, ψ])
    have hfst : descentρ₁ f T' ≫ pullback.fst _ _ = descentρ₂ f T' ≫ pullback.fst _ _ := by
      simp
    have hy : (descentMap (l := l) f γ).hom.hom.app (op T') y = 0 := by
      apply comps_injective
      rw [comps_descentMap, comps_zero, comps_ofComps]
      funext i
      refine Subtype.ext (ContinuousMap.ext fun q ↦ ?_)
      have e₁₃ : (tripleProj₁₃ f).base (Θ.base q) = ψ.base ((descentρ₂ f T').base q) := by
        rw [← Scheme.Hom.comp_apply, hΘ₁₃, Scheme.Hom.comp_apply]
      have e₁₂ : (pullback.fst (pullback.snd f f) (pullback.fst f f)).base (Θ.base q) =
          ψ.base ((descentρ₁ f T').base q) := by
        rw [← Scheme.Hom.comp_apply, hΘ₁₂, Scheme.Hom.comp_apply]
      have e₂₃ : (pullback.snd (pullback.snd f f) (pullback.fst f f)).base (Θ.base q) =
          (pullback.snd T'.hom (pullback.fst f f ≫ f)).base q := by
        rw [← Scheme.Hom.comp_apply, hΘ₂₃]
      have hc (k : Fin n) : (γ i k).1 (ψ.base ((descentρ₂ f T').base q)) =
          ∑ j, (γ i j).1 ((pullback.snd T'.hom (pullback.fst f f ≫ f)).base q) *
            (γ j k).1 (ψ.base ((descentρ₁ f T').base q)) := by
        have := congrArg (fun M ↦ (M i k).1 (Θ.base q)) hcoc
        simp only [Matrix.map_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
          ContinuousMap.sum_apply, MulMemClass.coe_mul, ContinuousMap.mul_apply,
          PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply] at this
        erw [e₁₃, e₁₂, e₂₃] at this
        exact this
      have hq : (pullback.fst T'.hom f).base ((descentρ₁ f T').base q) =
          (pullback.fst T'.hom f).base ((descentρ₂ f T').base q) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfst]
      simp only [Pi.zero_apply, ZeroMemClass.coe_zero, ContinuousMap.zero_apply,
        AddSubgroupClass.coe_sub, ContinuousMap.sub_apply, AddSubmonoidClass.coe_finsetSum,
        ContinuousMap.sum_apply, MulMemClass.coe_mul, ContinuousMap.mul_apply,
        PadicAlgCl.locallyFiniteFunctionsComp_apply_coe, ContinuousMap.comp_apply, yc]
      rw [sub_eq_zero]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      erw [hc k, ← hq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    obtain ⟨s, hs⟩ := exists_kernel_ι_eq (descentMap (l := l) f γ) T' y hy
    refine ⟨s, comps_injective (funext fun i ↦ Subtype.ext (ContinuousMap.ext fun x ↦ ?_))⟩
    change (comps ((⨁ fun _ : Fin n ↦ unit l W).X.obj.map u.op
      ((kernel.ι (descentMap (l := l) f γ)).hom.hom.app (op T') s)) i).1 x = _
    rw [hmap, hs, comps_ofComps]
    have hψu : u.left ≫ ψ = T.hom ≫ pullback.diagonal f := pullback.hom_ext
      (by simp only [ψ, Category.assoc, pullback.lift_fst, pullback.diagonal_fst]
          rw [← Category.assoc, hu₁]; exact Category.id_comp _)
      (by simp only [ψ, Category.assoc, pullback.lift_snd, pullback.diagonal_snd]
          rw [hu₂]; exact (Category.comp_id _).symm)
    have hd (j : Fin n) : (γ i j).1 (ψ.base (u.left.base x)) = if i = j then 1 else 0 := by
      have := congrArg (fun M ↦ (M i j).1 (T.hom.base x)) hdiag
      simp only [Matrix.map_apply, PadicAlgCl.locallyFiniteFunctionsComp_apply_coe,
        ContinuousMap.comp_apply, Matrix.one_apply] at this
      have e := congrArg (fun φ ↦ φ.base x) hψu
      simp only [Scheme.Hom.comp_apply] at e
      erw [e]
      refine this.trans ?_
      split_ifs <;> rfl
    have hf : (pullback.fst T'.hom f).base (u.left.base x) = x := by
      have e := congrArg (fun φ ↦ φ.base x) hu₁
      simp only [Scheme.Hom.comp_apply] at e
      exact e
    simp only [yc, AddSubmonoidClass.coe_finsetSum, ContinuousMap.sum_apply, MulMemClass.coe_mul,
      ContinuousMap.mul_apply, PadicAlgCl.locallyFiniteFunctionsComp_apply_coe,
      ContinuousMap.comp_apply]
    refine (Finset.sum_congr rfl fun j _ ↦
      (congrArg₂ (· * ·) (hd j) (congrArg (c j).1 hf) :)).trans ?_
    simp [c]

variable {f γ} in
/-- **The comparison `f^* G ⟶ ℚ̄_ℓ,Wⁿ` is an isomorphism**, being bijective on sections. -/
lemma isIso_descentTriv
    (hdiag : γ.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) = 1)
    (hcoc : γ.map (PadicAlgCl.locallyFiniteFunctionsComp l (tripleProj₁₃ f).base.hom) =
      γ.map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.snd (pullback.snd f f) (pullback.fst f f)).base.hom) *
      γ.map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.fst (pullback.snd f f) (pullback.fst f f)).base.hom)) :
    IsIso (descentTriv (l := l) f γ) := by
  have h : IsIso ((ProEtale.localizationRestriction _ f inferInstance).map
      (kernel.ι (descentMap (l := l) f γ)).hom ≫
      (ProEtale.localizationRestrictionLowerStarAdjunction _ f inferInstance).counit.app
        (⨁ fun _ : Fin n ↦ unit l W).X) := by
    have : IsIso ((sheafToPresheaf (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)).map
        ((ProEtale.localizationRestriction _ f inferInstance).map
          (kernel.ι (descentMap (l := l) f γ)).hom ≫
        (ProEtale.localizationRestrictionLowerStarAdjunction _ f inferInstance).counit.app
          (⨁ fun _ : Fin n ↦ unit l W).X)) := by
      have (U : W.ProEtᵒᵖ) : IsIso (((sheafToPresheaf (Scheme.ProEt.topology W)
          (WeilCoefficients.{u} l)).map ((ProEtale.localizationRestriction _ f inferInstance).map
            (kernel.ι (descentMap (l := l) f γ)).hom ≫
          (ProEtale.localizationRestrictionLowerStarAdjunction _ f inferInstance).counit.app
            (⨁ fun _ : Fin n ↦ unit l W).X)).app U) := by
        rw [ConcreteCategory.isIso_iff_bijective]
        have e : ((sheafToPresheaf (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)).map
            ((ProEtale.localizationRestriction _ f inferInstance).map
              (kernel.ι (descentMap (l := l) f γ)).hom ≫
            (ProEtale.localizationRestrictionLowerStarAdjunction _ f inferInstance).counit.app
              (⨁ fun _ : Fin n ↦ unit l W).X)).app U =
            ((ProEtale.localizationRestriction _ f inferInstance).map
              (kernel.ι (descentMap (l := l) f γ)).hom).hom.app U ≫
            ((ProEtale.localizationRestrictionLowerStarAdjunction _ f inferInstance).counit.app
              (⨁ fun _ : Fin n ↦ unit l W).X).hom.app U := rfl
        rw [e, localizationRestrictionLowerStarAdjunction_counit_app_hom_app]
        exact bijective_descentTrivApp (l := l) hdiag hcoc U.unop
      exact NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  have : IsIso ((Mod.forget _).map (descentTriv (l := l) f γ)) := by
    change IsIso (descentTriv (l := l) f γ).hom
    rw [descentTriv_hom]
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

end Descent

section Adjunctions

variable {X W P : Scheme.{u}}

/-- The adjunction `g^* ⊣ g_*` and the congruence isomorphisms for `g = g'`. -/
lemma homEquiv_adicUpperStarCongr {g g' : W ⟶ X} (h : g = g') {G : AdicSheaf l X}
    {K : AdicSheaf l W} (Z : (g')^*ᵃ[l].obj G ⟶ K) :
    (adicUpperStarLowerStarAdjunction l g).homEquiv G K
        ((adicUpperStarCongr l h).hom.app G ≫ Z) =
      (adicUpperStarLowerStarAdjunction l g').homEquiv G K Z ≫
        (adicLowerStarCongr l h.symm).hom.app K := by
  subst h
  simp only [adicUpperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  have : (adicLowerStarCongr l (rfl : g = g)).hom.app K = 𝟙 _ :=
    Mod.hom_ext _ _ (by rw [adicLowerStarCongr_hom_app_hom, lowerStarCongr_rfl]; rfl)
  rw [this, Category.comp_id]

/-- **Composites of adjunctions**: the adjoint of a composite of pullbacks is computed by the
composite of the adjoints. -/
lemma homEquiv_adicUpperStarComp (a : P ⟶ W) (f : W ⟶ X) {G : AdicSheaf l X} {M : AdicSheaf l W}
    {K : AdicSheaf l P} (ψ : (f)^*ᵃ[l].obj G ⟶ M) (Y : (a)^*ᵃ[l].obj M ⟶ K) :
    (adicUpperStarLowerStarAdjunction l (a ≫ f)).homEquiv G K
        ((adicUpperStarComp l a f).hom.app G ≫ (a)^*ᵃ[l].map ψ ≫ Y) =
      (adicUpperStarLowerStarAdjunction l f).homEquiv G M ψ ≫
        (f)_*ᵃ[l].map ((adicUpperStarLowerStarAdjunction l a).homEquiv M K Y) ≫
          (adicLowerStarComp l a f).hom.app K := by
  have hu := unit_conjugateEquiv ((adicUpperStarLowerStarAdjunction l f).comp
    (adicUpperStarLowerStarAdjunction l a)) (adicUpperStarLowerStarAdjunction l (a ≫ f))
    (adicUpperStarComp l a f).hom G
  rw [conjugateEquiv_adicUpperStarComp_hom] at hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu, Category.assoc,
    ← (adicLowerStarComp l a f).hom.naturality, ← Category.assoc,
    ← Adjunction.homEquiv_unit, Adjunction.comp_homEquiv]
  dsimp only
  erw [Equiv.trans_apply]
  have h₁ : (adicUpperStarLowerStarAdjunction l a).homEquiv _ _ ((a)^*ᵃ[l].map ψ ≫ Y) =
      ψ ≫ (adicUpperStarLowerStarAdjunction l a).homEquiv M K Y :=
    Adjunction.homEquiv_naturality_left _ _ _
  have h₂ : (adicUpperStarLowerStarAdjunction l f).homEquiv G ((a)_*ᵃ[l].obj K)
      (ψ ≫ (adicUpperStarLowerStarAdjunction l a).homEquiv M K Y) =
      (adicUpperStarLowerStarAdjunction l f).homEquiv G M ψ ≫
        (f)_*ᵃ[l].map ((adicUpperStarLowerStarAdjunction l a).homEquiv M K Y) :=
    Adjunction.homEquiv_naturality_right _ _ _
  exact (congrArg (· ≫ (adicLowerStarComp l a f).hom.app K)
    ((congrArg _ h₁).trans h₂)).trans (Category.assoc _ _ _)

end Adjunctions

variable {X W : Scheme.{u}}

/-- **Descent of trivial `ℓ`-adic sheaves along a pro-étale cover** (the stack property of
sheaves on the pro-étale site; SGA 4, Exp. VIII, 9.1, and Bhatt–Scholze, *The pro-étale topology
for schemes*, §4.2: the pro-étale site is subcanonical and sheaves glue). Let `f : W ⟶ X` be
weakly étale and `γ` a matrix of locally finite functions on `W ×_X W` which is a cocycle:
trivial on the diagonal and `γ₁₃ = γ₂₃ γ₁₂` on `W ×_X W ×_X W`. Then the descent datum on
`ℚ̄_ℓ,Wⁿ` given by `γ` is effective: there are an `ℓ`-adic sheaf `G` on `X` and a trivialisation
`ε : f^* G ≅ ℚ̄_ℓ,Wⁿ` whose transition matrix on `W ×_X W` is `γ`. The sheaf `G` is the kernel of
`f_* ℚ̄_ℓ,Wⁿ ⟶ (p₁ f)_* ℚ̄_ℓ,(W ×_X W)ⁿ`, `y ↦ γ · p₁^* y - p₂^* y`
(`AlgebraicGeometry.ProEtale.AdicSheaf.descentSheaf`). -/
theorem exists_iso_transitionMatrix_eq (f : W ⟶ X) [WeaklyEtale f] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) (PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback f f)))
    (hdiag : γ.map (PadicAlgCl.locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) = 1)
    (hcoc : γ.map (PadicAlgCl.locallyFiniteFunctionsComp l (tripleProj₁₃ f).base.hom) =
      γ.map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.snd (pullback.snd f f) (pullback.fst f f)).base.hom) *
      γ.map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.fst (pullback.snd f f) (pullback.fst f f)).base.hom)) :
    ∃ (G : AdicSheaf l X) (ε : (f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W),
      transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition = γ := by
  have := isIso_descentTriv (l := l) hdiag hcoc
  set ε := asIso (descentTriv (l := l) f γ)
  refine ⟨descentSheaf f γ, ε, ?_⟩
  have hε : (adicUpperStarLowerStarAdjunction l f).homEquiv _ _ ε.hom =
      kernel.ι (descentMap (l := l) f γ) := Equiv.apply_symm_apply _ _
  have key : (trivPull f ε (pullback.fst f f)).hom ≫ ofUnitMatrix γ =
      (adicUpperStarCongr l pullback.condition).hom.app _ ≫
        (trivPull f ε (pullback.snd f f)).hom := by
    apply ((adicUpperStarLowerStarAdjunction l (pullback.fst f f ≫ f)).homEquiv _ _).injective
    simp only [trivPull, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [homEquiv_adicUpperStarCongr, homEquiv_adicUpperStarComp, homEquiv_adicUpperStarComp, hε,
      Adjunction.homEquiv_naturality_right, ← freePull_eq, ← freePull_eq]
    have hk : kernel.ι (descentMap (l := l) f γ) ≫ descentMapFst f γ =
        kernel.ι (descentMap (l := l) f γ) ≫ descentMapSnd f := by
      have h0 : kernel.ι (descentMap (l := l) f γ) ≫ (descentMapFst f γ - descentMapSnd f) = 0 := by
        rw [← descentMap_eq]
        exact kernel.condition _
      rwa [Preadditive.comp_sub, sub_eq_zero] at h0
    simp only [descentMapFst, descentMapSnd, Functor.map_comp, Category.assoc] at hk ⊢
    exact hk
  rw [transitionMatrix, transitionHom_eq, ← key, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, unitMatrix_ofUnitMatrix]

end AdicSheaf

end AlgebraicGeometry.ProEtale
