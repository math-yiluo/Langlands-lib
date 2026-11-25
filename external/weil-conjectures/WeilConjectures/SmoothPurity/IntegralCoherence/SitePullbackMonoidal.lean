/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.SitePullbackTensorGenerators
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Monoidal structure of a ringed-site module pullback

Source: Stacks Project, Modules on Sites, Tag 03EL, and Cohomology on Sites, Tag 07A4.

For a continuous, representably flat functor of sites and a map of coefficient rings,
every left adjoint of the module direct image carries the pure-tensor normalized
comparison of `sitePullbackTensorGenerators`. All identities are checked on the
adjunction-unit images of pure tensors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

universe c v r uC vC w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.CochainPullback (moduleTmul moduleTmul_map moduleTmul_braiding
  moduleTmul_associator)

namespace WeilConjectures.SitePullbackMonoidal

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local instance 2000] SheafOfModules.cochainModulesSymmetric

section TensorExt

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- Morphisms out of a sheaf tensor product are determined on pure tensors. -/
theorem moduleTmul_hom_ext
    {M N H : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    {f g : M ⊗ N ⟶ H}
    (h : ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      f.val.app W (moduleTmul M N W m n) = g.val.app W (moduleTmul M N W m n)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h W m n

/-- Morphisms out of a triple sheaf tensor product are determined on pure triples. -/
theorem moduleTmul_hom_ext₃
    {M N P H : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    {f g : (M ⊗ N) ⊗ P ⟶ H}
    (h : ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) (p : P.val.obj W),
      f.val.app W (moduleTmul (M ⊗ N) P W (moduleTmul M N W m n) p) =
        g.val.app W (moduleTmul (M ⊗ N) P W (moduleTmul M N W m n) p)) : f = g := by
  let RB := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙 RB.obj)
  let Sh := PresheafOfModules.sheafification.{w} (𝟙 RB.obj)
  let η : M.val ⊗ N.val ⟶ (M ⊗ N).val :=
    adj.unit.app (M.val ⊗ N.val) ≫ (SheafOfModules.tensorObjIsoSheafification M N).inv.val
  have hη : (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)) η := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (𝟙 RB.obj)]
    have h₁ : IsIso (Sh.map (adj.unit.app (M.val ⊗ N.val))) := by
      dsimp only [Sh, adj]
      infer_instance
    have h₂ : IsIso (Sh.map (SheafOfModules.tensorObjIsoSheafification M N).inv.val) :=
      Functor.map_isIso Sh ((SheafOfModules.forget RB).map
        (SheafOfModules.tensorObjIsoSheafification M N).inv)
    change IsIso (Sh.map η)
    dsimp only [η]
    rw [Functor.map_comp]
    infer_instance
  have hw : IsIso (Sh.map (η ▷ P.val)) := by
    have h := MorphismProperty.IsMonoidal.whiskerRight
      (W := J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)) η hη P.val
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RB.obj)] at h
    exact h
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (M ⊗ N) P).inv).mp
  apply (cancel_epi (Sh.map (η ▷ P.val))).mp
  apply (adj.homEquiv _ H).injective
  have key (k : (M ⊗ N) ⊗ P ⟶ H) (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W)
      (p : P.val.obj W) :
      (adj.unit.app ((M.val ⊗ N.val) ⊗ P.val) ≫
        (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
          (Sh.map (η ▷ P.val) ≫ (SheafOfModules.tensorObjIsoSheafification (M ⊗ N) P).inv ≫
            k)).app W ((m ⊗ₜ n) ⊗ₜ p) =
        k.val.app W (moduleTmul (M ⊗ N) P W (moduleTmul M N W m n) p) := by
    have e : adj.unit.app ((M.val ⊗ N.val) ⊗ P.val) ≫
        (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
          (Sh.map (η ▷ P.val) ≫ (SheafOfModules.tensorObjIsoSheafification (M ⊗ N) P).inv ≫
            k) = (η ▷ P.val) ≫ adj.unit.app ((M ⊗ N).val ⊗ P.val) ≫
        (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
          ((SheafOfModules.tensorObjIsoSheafification (M ⊗ N) P).inv ≫ k) := by
      simp only [Functor.map_comp, ← Category.assoc]
      congr 2
      exact (adj.unit.naturality (η ▷ P.val)).symm
    exact (congrArg (fun q ↦ q.app W ((m ⊗ₜ n) ⊗ₜ p)) e).trans rfl
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro m n p
  exact (key f W m n p).trans ((h W m n p).trans (key g W m n p).symm)

/-- The monoidal unit of sheaves of modules is the unit sheaf of modules. -/
theorem tensorUnit_eq :
    𝟙_ (SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) =
      SheafOfModules.unit _ := rfl

/-- The forgetful functor to presheaves has trivial lax unit. -/
theorem forget_ε :
    letI := Adjunction.rightAdjointLaxMonoidal (PresheafOfModules.sheafificationAdjunction.{w}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj))
    Functor.LaxMonoidal.ε (SheafOfModules.forget
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)) = 𝟙 _ := by
  let RB := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙 RB.obj)
  have h : Functor.OplaxMonoidal.η (PresheafOfModules.sheafification.{w} (𝟙 RB.obj)) =
      adj.counit.app (𝟙_ _) := rfl
  change adj.homEquiv _ _ (Functor.OplaxMonoidal.η _) = _
  rw [h, Adjunction.homEquiv_unit]
  exact adj.right_triangle_components (𝟙_ _)

/-- The left unitor acts on pure tensors by scalar multiplication. -/
theorem moduleTmul_leftUnitor
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (W : Cᵒᵖ) (a : R.obj.obj W) (x : M.val.obj W) :
    (λ_ M).hom.val.app W (moduleTmul (𝟙_ _) M W a x) = a • x := by
  let RB := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙 RB.obj)
  let V := SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)
  let : V.LaxMonoidal := adj.rightAdjointLaxMonoidal
  have h := Functor.LaxMonoidal.left_unitality V M
  rw [forget_ε, id_whiskerRight, Category.id_comp] at h
  exact congrArg (fun k ↦ k.app W (a ⊗ₜ[R.obj.obj W] x)) h.symm

/-- The right unitor acts on pure tensors by scalar multiplication. -/
theorem moduleTmul_rightUnitor
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (W : Cᵒᵖ) (x : M.val.obj W) (a : R.obj.obj W) :
    (ρ_ M).hom.val.app W (moduleTmul M (𝟙_ _) W x a) = a • x := by
  let RB := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙 RB.obj)
  let V := SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)
  let : V.LaxMonoidal := adj.rightAdjointLaxMonoidal
  have h := Functor.LaxMonoidal.right_unitality V M
  rw [forget_ε, MonoidalCategory.whiskerLeft_id, Category.id_comp] at h
  exact congrArg (fun k ↦ k.app W (x ⊗ₜ[R.obj.obj W] a)) h.symm

/-- Restriction of pure tensors. -/
theorem moduleTmul_restrict
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    {W V : Cᵒᵖ} (i : W ⟶ V) (x : M.val.obj W) (y : N.val.obj W) :
    (M ⊗ N).val.map i (moduleTmul M N W x y) =
      moduleTmul M N V (M.val.map i x) (N.val.map i y) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  let t := x ⊗ₜ[R.obj.obj W] y
  have hi := PresheafOfModules.naturality_apply
    (SheafOfModules.tensorObjIsoSheafification M N).inv.val i
      ((adj.unit.app (M.val ⊗ N.val)).app W t)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i t
  exact hi.symm.trans
    (congrArg ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app V) hu.symm)

/-- Evaluation of a composite of sheaf-module morphisms on a section. -/
theorem comp_val_app_apply {A B T : SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (f : A ⟶ B) (g : B ⟶ T)
    (W : Cᵒᵖ) (z : A.val.obj W) : (f ≫ g).val.app W z = g.val.app W (f.val.app W z) := rfl

/-- Evaluation of an identity of sheaf modules on a section. -/
theorem id_val_app_apply {A : SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (W : Cᵒᵖ) (z : A.val.obj W) : (𝟙 A : A ⟶ A).val.app W z = z := rfl

end TensorExt

section RingMap

variable [UnivLE.{max c v, r}] {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
  (φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)

/-- The coefficient map as a map of sheaves of rings, with its pushforward target. -/
def ringMap : (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R ⟶
    (U.sheafPushforwardContinuous RingCat.{r} J K).obj
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ

end RingMap

section Generic

variable [UnivLE.{max c v, r}]
  {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]
  (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
  (φ : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{r} J K).obj S)
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  [F.Additive]
  (adj : F ⊣ SheafOfModules.pushforward.{r} (ringMap J K U R S φ))

/-- The pure-tensor normalized ordinary comparison `F (M ⊗ N) ≅ F M ⊗ F N`. -/
def ordinary (M N : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N :=
  (SemilinearSections.sitePullbackTensorGenerators J K U R S φ F adj).exists.choose.ordinary M N

/-- The ordinary comparison sends the unit image of a pure tensor to the pure tensor
of the unit images. -/
theorem ordinary_pure (M N : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)) :
    (ordinary J K U R S φ F adj M N).hom.val.app (op (U.obj V))
        ((adj.unit.app (M ⊗ N)).val.app (op V) (moduleTmul M N (op V) x y)) =
      moduleTmul (F.obj M) (F.obj N) (op (U.obj V))
        ((adj.unit.app M).val.app (op V) x) ((adj.unit.app N).val.app (op V) y) := by
  have h := (SemilinearSections.sitePullbackTensorGenerators J K U R S φ F
    adj).exists.choose.normalized.1 M N V (U.obj V) (𝟙 _) x y 1
  simp only [op_id, PresheafOfModules.map_id, one_smul] at h
  exact h

/-- Naturality of the ordinary comparison in both variables. -/
theorem ordinary_natural {M M' N N' : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (a : M ⟶ M') (b : N ⟶ N') :
    F.map (a ⊗ₘ b) ≫ (ordinary J K U R S φ F adj M' N').hom =
      (ordinary J K U R S φ F adj M N).hom ≫ (F.map a ⊗ₘ F.map b) :=
  (SemilinearSections.sitePullbackTensorGenerators J K U R S φ F
    adj).exists.choose.normalized.2 M M' N N' a b

include adj in
/-- Naturality of the adjunction unit, evaluated on a section. -/
theorem unit_naturality_apply {A B : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)} (g : A ⟶ B)
    (V : C) (a : A.val.obj (op V)) :
    (F.map g).val.app (op (U.obj V)) ((adj.unit.app A).val.app (op V) a) =
      (adj.unit.app B).val.app (op V) (g.val.app (op V) a) :=
  (congrArg (fun k ↦ k.val.app (op V) a) (adj.unit.naturality g)).symm

/-- Maps out of the pullback of a tensor product are determined on unit images of pure
tensors. -/
theorem hom_ext_pure {M N : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
    {a b : F.obj (M ⊗ N) ⟶ T}
    (h : ∀ (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
      a.val.app (op (U.obj V)) ((adj.unit.app (M ⊗ N)).val.app (op V)
          (moduleTmul M N (op V) x y)) =
        b.val.app (op (U.obj V)) ((adj.unit.app (M ⊗ N)).val.app (op V)
          (moduleTmul M N (op V) x y))) :
    a = b := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply moduleTmul_hom_ext
  intro W x y
  exact h W.unop x y

/-- Maps out of the pullback of a triple tensor product are determined on unit images of
pure triples. -/
theorem hom_ext_pure₃ {M N P : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {T : SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
    {a b : F.obj ((M ⊗ N) ⊗ P) ⟶ T}
    (h : ∀ (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)) (z : P.val.obj (op V)),
      a.val.app (op (U.obj V)) ((adj.unit.app ((M ⊗ N) ⊗ P)).val.app (op V)
          (moduleTmul (M ⊗ N) P (op V) (moduleTmul M N (op V) x y) z)) =
        b.val.app (op (U.obj V)) ((adj.unit.app ((M ⊗ N) ⊗ P)).val.app (op V)
          (moduleTmul (M ⊗ N) P (op V) (moduleTmul M N (op V) x y) z))) :
    a = b := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply moduleTmul_hom_ext₃
  intro W x y z
  exact h W.unop x y z

/-- The unit comparison `F 𝟙 ⟶ 𝟙`, adjoint to the coefficient map. -/
def unitMap₀ : F.obj (SheafOfModules.unit _) ⟶ SheafOfModules.unit _ :=
  (adj.homEquiv _ _).symm (SheafOfModules.unitToPushforwardObjUnit (ringMap J K U R S φ))

instance unitMap₀_isIso : IsIso (unitMap₀ J K U R S φ F adj) := by
  have : U.Final := final_of_representablyFlat U
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← (adj.homEquiv _ _).bijective.of_comp_iff',
    ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert! (SheafOfModules.bijective_pushforwardSections (ringMap J K U R S φ) M).comp
      (SheafOfModules.unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [SheafOfModules.pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right, unitMap₀, Equiv.apply_symm_apply]

/-- The unit comparison, between the monoidal units. -/
def unitMap : F.obj (𝟙_ (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⟶
    𝟙_ (SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) :=
  unitMap₀ J K U R S φ F adj

instance unitMap_isIso : IsIso (unitMap J K U R S φ F adj) :=
  unitMap₀_isIso J K U R S φ F adj

/-- The unit comparison sends the unit image of a scalar to its image in the target ring. -/
theorem unitMap_apply (V : C) (a : R.obj.obj (op V)) :
    (unitMap J K U R S φ F adj).val.app (op (U.obj V))
        ((adj.unit.app (𝟙_ (SheafOfModules.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))).val.app (op V) a) =
      φ.hom.app (op V) a := by
  have h := (adj.homEquiv_unit _ _ (unitMap₀ J K U R S φ F adj)).symm
  rw [unitMap₀, Equiv.apply_symm_apply] at h
  exact congrArg (fun k ↦ k.val.app (op V) a) h

/-- The ordinary comparison is compatible with the symmetry. -/
theorem ordinary_braiding (M N : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    F.map (β_ M N).hom ≫ (ordinary J K U R S φ F adj N M).hom =
      (ordinary J K U R S φ F adj M N).hom ≫ (β_ (F.obj M) (F.obj N)).hom := by
  apply hom_ext_pure J K U R S φ F adj
  intro V x y
  simp only [comp_val_app_apply]
  rw [unit_naturality_apply, moduleTmul_braiding, ordinary_pure, ordinary_pure,
    moduleTmul_braiding]

/-- The ordinary comparison is compatible with the associators. -/
theorem ordinary_associativity (M N P : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    F.map (α_ M N P).hom ≫ (ordinary J K U R S φ F adj M (N ⊗ P)).hom ≫
        (F.obj M ◁ (ordinary J K U R S φ F adj N P).hom) =
      (ordinary J K U R S φ F adj (M ⊗ N) P).hom ≫
        ((ordinary J K U R S φ F adj M N).hom ▷ F.obj P) ≫
          (α_ (F.obj M) (F.obj N) (F.obj P)).hom := by
  rw [← id_tensorHom, ← tensorHom_id]
  apply hom_ext_pure₃ J K U R S φ F adj
  intro V x y z
  simp only [comp_val_app_apply, unit_naturality_apply, moduleTmul_associator,
    ordinary_pure, moduleTmul_map, id_val_app_apply]

/-- The ordinary comparison is compatible with the left unitors. -/
theorem ordinary_leftUnitor (M : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    F.map (λ_ M).hom = (ordinary J K U R S φ F adj _ M).hom ≫
      (unitMap J K U R S φ F adj ▷ F.obj M) ≫ (λ_ (F.obj M)).hom := by
  rw [← tensorHom_id]
  apply hom_ext_pure J K U R S φ F adj
  intro V a x
  simp only [comp_val_app_apply]
  rw [unit_naturality_apply, moduleTmul_leftUnitor, ordinary_pure, moduleTmul_map,
    unitMap_apply, id_val_app_apply, moduleTmul_leftUnitor]
  exact ((adj.unit.app M).val.app (op V)).hom.map_smul a x

/-- The ordinary comparison is compatible with the right unitors. -/
theorem ordinary_rightUnitor (M : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    F.map (ρ_ M).hom = (ordinary J K U R S φ F adj M _).hom ≫
      (F.obj M ◁ unitMap J K U R S φ F adj) ≫ (ρ_ (F.obj M)).hom := by
  rw [← id_tensorHom]
  apply hom_ext_pure J K U R S φ F adj
  intro V x a
  simp only [comp_val_app_apply]
  rw [unit_naturality_apply, moduleTmul_rightUnitor, ordinary_pure, moduleTmul_map,
    unitMap_apply, id_val_app_apply, moduleTmul_rightUnitor]
  exact ((adj.unit.app M).val.app (op V)).hom.map_smul a x

/-- The monoidal structure on the module pullback given by the normalized comparison. -/
def coreMonoidal : F.CoreMonoidal where
  εIso := (asIso (unitMap J K U R S φ F adj)).symm
  μIso M N := (ordinary J K U R S φ F adj M N).symm
  μIso_hom_natural_left f X' := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    simp only [← tensorHom_id]
    rw [ordinary_natural J K U R S φ F adj, F.map_id]
  μIso_hom_natural_right X' f := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    simp only [← id_tensorHom]
    rw [ordinary_natural J K U R S φ F adj, F.map_id]
  associativity X Y Z := by
    have h := ordinary_associativity J K U R S φ F adj X Y Z
    simp only [Iso.symm_hom]
    rw [← cancel_mono ((ordinary J K U R S φ F adj X (Y ⊗ Z)).hom ≫
        (F.obj X ◁ (ordinary J K U R S φ F adj Y Z).hom)),
      ← cancel_epi ((ordinary J K U R S φ F adj (X ⊗ Y) Z).hom ≫
        ((ordinary J K U R S φ F adj X Y).hom ▷ F.obj Z))]
    simp only [Category.assoc, hom_inv_whiskerRight_assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc, whiskerLeft_inv_hom, Category.comp_id]
    exact h
  left_unitality X := by
    rw [ordinary_leftUnitor J K U R S φ F adj X]
    simp only [Iso.symm_hom, asIso_inv, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc,
      IsIso.inv_hom_id, id_whiskerRight, Category.id_comp]
  right_unitality X := by
    rw [ordinary_rightUnitor J K U R S φ F adj X]
    simp only [Iso.symm_hom, asIso_inv, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The monoidal structure on the module pullback. -/
@[instance_reducible]
def monoidal : F.Monoidal := (coreMonoidal J K U R S φ F adj).toMonoidal

theorem monoidal_δ (M N : SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F
        (monoidal J K U R S φ F adj).toOplaxMonoidal M N =
      (ordinary J K U R S φ F adj M N).hom := rfl

end Generic

section Composition

variable [UnivLE.{max c v, r}]
  {C D E : Type c} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D] [EssentiallySmall.{r} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {U₁ : C ⥤ D} [U₁.IsContinuous J K] [RepresentablyFlat U₁]
  {U₂ : D ⥤ E} [U₂.IsContinuous K L] [RepresentablyFlat U₂]
  {U₁₂ : C ⥤ E} [U₁₂.IsContinuous J L] [RepresentablyFlat U₁₂]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}} {T : Sheaf L CommRingCat.{r}}
  {φ₁ : R ⟶ (U₁.sheafPushforwardContinuous CommRingCat.{r} J K).obj S}
  {φ₂ : S ⟶ (U₂.sheafPushforwardContinuous CommRingCat.{r} K L).obj T}
  {φ₁₂ : R ⟶ (U₁₂.sheafPushforwardContinuous CommRingCat.{r} J L).obj T}
  {F₁ : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
  [F₁.Additive]
  {F₂ : SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S) ⥤
    SheafOfModules.{r} ((sheafCompose L (forget₂ CommRingCat.{r} RingCat.{r})).obj T)}
  [F₂.Additive]
  {F₁₂ : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose L (forget₂ CommRingCat.{r} RingCat.{r})).obj T)}
  [F₁₂.Additive]
  (adj₁ : F₁ ⊣ SheafOfModules.pushforward.{r} (ringMap J K U₁ R S φ₁))
  (adj₂ : F₂ ⊣ SheafOfModules.pushforward.{r} (ringMap K L U₂ S T φ₂))
  (adj₁₂ : F₁₂ ⊣ SheafOfModules.pushforward.{r} (ringMap J L U₁₂ R T φ₁₂))

/-- A compositor sending unit images to restricted iterated unit images is compatible with
the normalized ordinary comparisons. -/
theorem ordinary_composition (a : F₁₂ ≅ F₁ ⋙ F₂)
    (θ : ∀ V : C, U₁₂.obj V ⟶ U₂.obj (U₁.obj V))
    (ha : ∀ (M : SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
      (V : C) (x : M.val.obj (op V)),
      (a.hom.app M).val.app (op (U₁₂.obj V)) ((adj₁₂.unit.app M).val.app (op V) x) =
        (F₂.obj (F₁.obj M)).val.map (θ V).op
          ((adj₂.unit.app (F₁.obj M)).val.app (op (U₁.obj V))
            ((adj₁.unit.app M).val.app (op V) x)))
    (M N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    (ordinary J L U₁₂ R T φ₁₂ F₁₂ adj₁₂ M N).hom ≫ (a.hom.app M ⊗ₘ a.hom.app N) =
      a.hom.app (M ⊗ N) ≫ F₂.map (ordinary J K U₁ R S φ₁ F₁ adj₁ M N).hom ≫
        (ordinary K L U₂ S T φ₂ F₂ adj₂ (F₁.obj M) (F₁.obj N)).hom := by
  apply hom_ext_pure J L U₁₂ R T φ₁₂ F₁₂ adj₁₂
  intro V x y
  simp only [comp_val_app_apply, ordinary_pure, moduleTmul_map, ha]
  erw [← moduleTmul_restrict]
  erw [PresheafOfModules.naturality_apply,
    unit_naturality_apply.{c, v, r} K L U₂ S T φ₂ F₂ adj₂]
  rw [ordinary_pure]
  erw [PresheafOfModules.naturality_apply]
  erw [ordinary_pure]
  rfl

end Composition

end WeilConjectures.SitePullbackMonoidal
