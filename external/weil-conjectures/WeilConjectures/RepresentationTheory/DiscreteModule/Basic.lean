/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Discrete modules and continuous group cohomology

Let `G` be a topological group. A *discrete `G`-module* is an abelian group `M` with an action
of `G` by additive automorphisms such that every element of `M` has an open stabilizer. They form
a full subcategory `DiscreteModule G` of `Action AddCommGrpCat G`, which is abelian.

## Main definitions

- `Action.IsDiscreteModule`: the property of having open stabilizers.
- `DiscreteModule G`: the abelian category of discrete `G`-modules.
- `DiscreteModule.trivial`: an abelian group with the trivial action.
- `DiscreteModule.invariants`: the invariants functor `M ↦ Mᴳ`.
- `DiscreteModule.coind₁`: the coinduction functor from abelian groups, right adjoint to the
  forgetful functor; it sends injective abelian groups to injective objects, so
  `DiscreteModule G` has enough injectives.
- `DiscreteModule.H`: the continuous cohomology `Hⁿ(G, M) = Extⁿ(ℤ, M)`, the right derived
  functors of the invariants functor.

## Implementation notes

The blueprint (`def-exc-continuous-cohomology`) works with discrete modules over a finite
coefficient ring `A`. We work with `ℤ`-coefficients throughout: a discrete `A`-module with an
`A`-linear action is in particular a discrete `G`-module, and all statements we need (vanishing of
cohomology of torsion modules) are about the underlying abelian groups. For a module killed by
`n`, such as an `A`-module with `n = 0` in `A`, the cohomology groups are killed by `n`
(`DiscreteModule.zsmul_eq_zero_of_forall_zsmul_eq_zero`). The equivalent description by
continuous inhomogeneous cochains is not formalised.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace Action

variable {G : Type u} [Group G]

@[simp]
lemma ρ_mul_apply (M : Action AddCommGrpCat.{w} G) (a b : G) (x : M.V) :
    (M.ρ (a * b)).asHom.hom x = (M.ρ a).asHom.hom ((M.ρ b).asHom.hom x) := by
  rw [map_mul]
  rfl

@[simp]
lemma ρ_one_apply (M : Action AddCommGrpCat.{w} G) (x : M.V) : (M.ρ 1).asHom.hom x = x := by
  rw [map_one]
  rfl

@[simp]
lemma ρ_inv_apply_apply (M : Action AddCommGrpCat.{w} G) (a : G) (x : M.V) :
    (M.ρ a⁻¹).asHom.hom ((M.ρ a).asHom.hom x) = x := by
  rw [← ρ_mul_apply, inv_mul_cancel, ρ_one_apply]

@[simp]
lemma ρ_apply_inv_apply (M : Action AddCommGrpCat.{w} G) (a : G) (x : M.V) :
    (M.ρ a).asHom.hom ((M.ρ a⁻¹).asHom.hom x) = x := by
  rw [← ρ_mul_apply, mul_inv_cancel, ρ_one_apply]

lemma hom_comm_apply {M N : Action AddCommGrpCat.{w} G} (f : M ⟶ N) (g : G) (x : M.V) :
    f.hom.hom ((M.ρ g).asHom.hom x) = (N.ρ g).asHom.hom (f.hom.hom x) :=
  congr($(f.comm g).hom x)

/-- The stabilizer of an element of an abelian group with an action of `G`. -/
def stabilizer (M : Action AddCommGrpCat.{w} G) (x : M.V) : Subgroup G where
  carrier := {g | (M.ρ g).asHom.hom x = x}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by simp_all
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    simp

@[simp]
lemma mem_stabilizer {M : Action AddCommGrpCat.{w} G} {x : M.V} {g : G} :
    g ∈ M.stabilizer x ↔ (M.ρ g).asHom.hom x = x :=
  Iff.rfl

variable [TopologicalSpace G]

/-- An action of a topological group `G` on an abelian group is *discrete* if the stabilizer of
every element is open. -/
def IsDiscreteModule : ObjectProperty (Action AddCommGrpCat.{w} G) :=
  fun M ↦ ∀ x : M.V, IsOpen (M.stabilizer x : Set G)

end Action

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The category of discrete `G`-modules: abelian groups with an action of the topological group
`G` such that every element has an open stabilizer. It is abelian, its invariants functor is
`DiscreteModule.invariants`, and its cohomology `DiscreteModule.H` is the right derived functor
of the invariants, computed as `Ext` from the trivial module `ℤ`. We use `ℤ`-coefficients
instead of the finite coefficient ring `A` of the blueprint; see the implementation notes.
(blueprint: `def-exc-continuous-cohomology`) -/
abbrev DiscreteModule :=
  (Action.IsDiscreteModule.{max u w} (G := G)).FullSubcategory

namespace DiscreteModule

variable {G}

open Action

section

variable (M : DiscreteModule.{w} G)

lemma isOpen_stabilizer (x : M.obj.V) : IsOpen (M.obj.stabilizer x : Set G) :=
  M.property x

end

variable [IsTopologicalGroup G]

instance : (IsDiscreteModule.{max u w} (G := G)).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY x := by
    have : Mono ((Action.forget AddCommGrpCat.{max u w} G).map f) := inferInstance
    have hinj : Function.Injective f.hom.hom :=
      (AddCommGrpCat.mono_iff_injective _).1 this
    convert hY (f.hom.hom x) using 2
    ext g
    simp only [mem_stabilizer, ← hom_comm_apply]
    exact hinj.eq_iff.symm

instance : (IsDiscreteModule.{max u w} (G := G)).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX y := by
    have : Epi ((Action.forget AddCommGrpCat.{max u w} G).map f) := inferInstance
    have hsurj : Function.Surjective f.hom.hom :=
      (AddCommGrpCat.epi_iff_surjective _).1 this
    obtain ⟨x, rfl⟩ := hsurj y
    refine Subgroup.isOpen_mono (fun g (hg : _ = _) ↦ ?_) (hX x)
    simp [← hom_comm_apply, hg]

omit [IsTopologicalGroup G] in
lemma isDiscreteModule_of_isZero (X : Action AddCommGrpCat.{max u w} G) (hX : IsZero X) :
    IsDiscreteModule X := by
  have : Subsingleton X.V := AddCommGrpCat.isZero_iff_subsingleton.1
    ((Action.forget AddCommGrpCat.{max u w} G).map_isZero hX)
  intro x
  convert isOpen_univ (X := G)
  ext g
  simp only [SetLike.mem_coe, mem_stabilizer, Set.mem_univ, iff_true]
  exact Subsingleton.elim _ _

instance : (IsDiscreteModule.{max u w} (G := G)).ContainsZero where
  exists_zero := ⟨_, isZero_zero _, isDiscreteModule_of_isZero _ (isZero_zero _)⟩

instance : (IsDiscreteModule.{max u w} (G := G)).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro X ⟨p⟩ x
    let F := Action.forget AddCommGrpCat.{max u w} G ⋙ CategoryTheory.forget AddCommGrpCat.{max u w}
    have hlim := isLimitOfPreserves F p.isLimit
    refine Subgroup.isOpen_mono (H₁ := ⨅ j : Discrete J, (p.diag.obj j).stabilizer
      ((p.π.app j).hom.hom x)) ?_ ?_
    · intro g hg
      simp only [Subgroup.mem_iInf, mem_stabilizer] at hg
      refine (Types.isLimitEquivSections hlim).injective ?_
      ext j
      simp only [Types.isLimitEquivSections_apply]
      exact (hom_comm_apply (p.π.app j) g x).trans (hg j)
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun j ↦ p.prop_diag_obj j _⟩

noncomputable example : Abelian (DiscreteModule.{w} G) := inferInstance

variable (G) in
/-- The forgetful functor from discrete `G`-modules to abelian groups. -/
abbrev forget₂Ab : DiscreteModule.{w} G ⥤ AddCommGrpCat.{max u w} :=
  (IsDiscreteModule.{max u w} (G := G)).ι ⋙ Action.forget AddCommGrpCat.{max u w} G

instance : (IsDiscreteModule.{max u w} (G := G)).ι.Additive where

instance : PreservesFiniteLimits (IsDiscreteModule.{max u w} (G := G)).ι :=
  have := (IsDiscreteModule.{max u w} (G := G)).preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels _

instance : PreservesFiniteColimits (IsDiscreteModule.{max u w} (G := G)).ι :=
  have := (IsDiscreteModule.{max u w} (G := G)).preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels _

example : (forget₂Ab.{w} G).Additive := inferInstance
instance : PreservesFiniteLimits (forget₂Ab.{w} G) := comp_preservesFiniteLimits _ _
instance : PreservesFiniteColimits (forget₂Ab.{w} G) := comp_preservesFiniteColimits _ _
example : (forget₂Ab.{w} G).Faithful := inferInstance

variable (G) in
/-- The abelian group `A` with the trivial action of `G`, as a discrete `G`-module. -/
def trivial (A : AddCommGrpCat.{max u w}) : DiscreteModule.{w} G :=
  ⟨Action.trivial G A, fun x ↦ by
    convert isOpen_univ (X := G)
    ext g
    simp only [SetLike.mem_coe, mem_stabilizer, Set.mem_univ, iff_true]
    rfl⟩

section coind

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

variable (G) in
/-- The subgroup of `g : G` such that `f (x * g) = f x` for all `x`. -/
def rightStab {A : Type*} (f : G → A) : Subgroup G where
  carrier := {g | ∀ x, f (x * g) = f x}
  one_mem' := by simp
  mul_mem' {a b} ha hb x := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha x := by simpa using (ha (x * a⁻¹)).symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma mem_rightStab {A : Type*} {f : G → A} {g : G} :
    g ∈ rightStab G f ↔ ∀ x, f (x * g) = f x :=
  Iff.rfl

variable (G A) in
/-- The functions `G → A` invariant under right translation by an open subgroup of `G`. -/
def smoothFunctions : AddSubgroup (G → A) where
  carrier := {f | IsOpen (rightStab G f : Set G)}
  zero_mem' := by
    change IsOpen _
    convert isOpen_univ (X := G)
    ext
    simp [mem_rightStab]
  add_mem' {f₁ f₂} h₁ h₂ := by
    refine Subgroup.isOpen_mono (H₁ := rightStab G f₁ ⊓ rightStab G f₂) ?_ ?_
    · intro g hg x
      simp [hg.1 x, hg.2 x]
    · rw [Subgroup.coe_inf]
      exact h₁.inter h₂
  neg_mem' {f} h := by
    have : rightStab G (-f) = rightStab G f := by
      ext g
      simp only [mem_rightStab, Pi.neg_apply, neg_inj]
    change IsOpen _
    rw [this]
    exact h

lemma isOpen_rightStab_comp_mul {A : Type*} {f : G → A} (hf : IsOpen (rightStab G f : Set G))
    (g : G) :
    IsOpen (rightStab G (fun x ↦ f (x * g)) : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hc : Continuous fun v : G ↦ g⁻¹ * v * g := by fun_prop
  refine Filter.mem_of_superset ((hf.preimage hc).mem_nhds (by
    simp only [Set.mem_preimage]; simp)) ?_
  intro v hv x
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_rightStab] at hv
  simpa [mul_assoc] using hv (x * g)

/-- Right translation by `g` on smooth functions. -/
@[simps]
def translate (g : G) : smoothFunctions G A →+ smoothFunctions G A where
  toFun f := ⟨fun x ↦ f.1 (x * g), isOpen_rightStab_comp_mul f.2 g⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Postcomposition with an additive map on smooth functions. -/
@[simps]
def smoothFunctionsMap (φ : A →+ B) : smoothFunctions G A →+ smoothFunctions G B where
  toFun f := ⟨fun x ↦ φ (f.1 x), Subgroup.isOpen_mono (H₁ := rightStab G f.1)
    (fun g hg x ↦ by simp [(mem_rightStab.1 hg) x]) f.2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

end coind

variable (G) in
/-- The smooth functions `G → A`, with `G` acting by right translation. -/
@[simps]
def coind₁Action (A : AddCommGrpCat.{max u w}) : Action AddCommGrpCat.{max u w} G where
  V := AddCommGrpCat.of (smoothFunctions G A)
  ρ :=
    { toFun g := .of <| AddCommGrpCat.ofHom (translate g)
      map_one' := End.ext <| AddCommGrpCat.ext fun f ↦ Subtype.ext (funext fun x ↦ by
        simp [End.one_asHom])
      map_mul' a b := End.ext <| AddCommGrpCat.ext fun f ↦ Subtype.ext (funext fun x ↦ by
        simp [End.mul_asHom, mul_assoc]) }

lemma coind₁Action_stabilizer (A : AddCommGrpCat.{max u w}) (f : (coind₁Action G A).V) :
    (coind₁Action G A).stabilizer f = rightStab G f.1 := by
  ext g
  simp only [mem_stabilizer, mem_rightStab]
  change (translate g f = f) ↔ _
  exact ⟨fun h x ↦ congr_fun (congrArg Subtype.val h) x, fun h ↦ Subtype.ext (funext h)⟩

variable (G) in
/-- The coinduced discrete module of an abelian group `A`: the smooth functions `G → A`, with
`G` acting by right translation. -/
def coind₁Obj (A : AddCommGrpCat.{max u w}) : DiscreteModule.{w} G :=
  ⟨coind₁Action G A, fun f ↦ by
    rw [coind₁Action_stabilizer]
    exact f.2⟩

variable (G) in
/-- The coinduction functor from abelian groups to discrete `G`-modules, `A ↦ C^sm(G, A)`. It is
right adjoint to the forgetful functor (`DiscreteModule.coind₁Adjunction`). -/
@[simps obj]
def coind₁ : AddCommGrpCat.{max u w} ⥤ DiscreteModule.{w} G where
  obj := coind₁Obj G
  map φ := ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (smoothFunctionsMap φ.hom)
      comm g := rfl }

/-- The map `X ⟶ C^sm(G, A)`, `x ↦ (g ↦ φ (g • x))`, adjoint to `φ : X ⟶ A`. -/
def coind₁Lift {X : DiscreteModule.{w} G} {A : AddCommGrpCat.{max u w}} (φ : X.obj.V ⟶ A) :
    X ⟶ (coind₁ G).obj A :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun x := ⟨fun g ↦ φ.hom ((X.obj.ρ g).asHom.hom x), Subgroup.isOpen_mono
            (H₁ := X.obj.stabilizer x) (fun u hu y ↦ by simp [mem_stabilizer.1 hu])
            (X.isOpen_stabilizer x)⟩
          map_zero' := by ext; simp
          map_add' _ _ := by ext; simp }
      comm g := AddCommGrpCat.ext fun x ↦ Subtype.ext (funext fun y ↦ by
        change φ.hom ((X.obj.ρ y).asHom.hom ((X.obj.ρ g).asHom.hom x)) =
          φ.hom ((X.obj.ρ (y * g)).asHom.hom x)
        simp) }

@[simp]
lemma coind₁Lift_apply {X : DiscreteModule.{w} G} {A : AddCommGrpCat.{max u w}}
    (φ : X.obj.V ⟶ A) (x : X.obj.V) (g : G) :
    ((coind₁Lift φ).hom.hom.hom x).1 g = φ.hom ((X.obj.ρ g).asHom.hom x) :=
  rfl

variable (G) in
/-- Evaluation at `1` on smooth functions. -/
def eval₁ (A : AddCommGrpCat.{max u w}) : ((coind₁ G).obj A).obj.V ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun f := f.1 1
      map_zero' := rfl
      map_add' _ _ := rfl }

@[simp]
lemma eval₁_apply (A : AddCommGrpCat.{max u w}) (f : ((coind₁ G).obj A).obj.V) :
    (eval₁ G A).hom f = f.1 1 :=
  rfl

variable (G) in
/-- The forgetful functor is left adjoint to coinduction. -/
def coind₁Adjunction : forget₂Ab.{w} G ⊣ coind₁ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv X A :=
        { toFun := coind₁Lift
          invFun F := (forget₂Ab G).map F ≫ eval₁ G A
          left_inv φ := by
            ext x
            change φ.hom ((X.obj.ρ 1).asHom.hom x) = φ.hom x
            simp
          right_inv F := by
            ext x
            refine Subtype.ext (funext fun g ↦ ?_)
            change ((F.hom.hom.hom ((X.obj.ρ g).asHom.hom x))).1 1 = (F.hom.hom.hom x).1 g
            rw [hom_comm_apply]
            change (F.hom.hom.hom x).1 (1 * g) = _
            rw [one_mul] }
      homEquiv_naturality_left_symm f g := rfl
      homEquiv_naturality_right f g := rfl }

instance : (coind₁.{w} G).Additive where
  map_add := rfl

lemma surjective_smoothFunctionsMap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (hφ : Function.Surjective φ) :
    Function.Surjective (smoothFunctionsMap (G := G) φ) := by
  intro f
  let U : Subgroup G := rightStab G f.1
  let rep : G → G := fun x ↦ Quotient.out (QuotientGroup.mk x : G ⧸ U)
  have hrep (x : G) : x⁻¹ * rep x ∈ U :=
    QuotientGroup.leftRel_apply.1
      (Quotient.exact (Quotient.out_eq (QuotientGroup.mk x : G ⧸ U)).symm)
  have hrep' (x : G) (u : G) (hu : u ∈ U) : rep (x * u) = rep x := by
    simp only [rep]
    congr 1
    exact QuotientGroup.eq.2 (by simpa using hu)
  refine ⟨⟨fun x ↦ Function.surjInv hφ (f.1 (rep x)), Subgroup.isOpen_mono (H₁ := U)
    (fun u hu x ↦ by simp only; rw [hrep' x u hu]) f.2⟩, ?_⟩
  refine Subtype.ext (funext fun x ↦ ?_)
  simp only [smoothFunctionsMap_apply_coe, Function.surjInv_eq]
  have := mem_rightStab.1 (hrep x) x
  rwa [mul_inv_cancel_left] at this

instance : (coind₁.{w} G).PreservesEpimorphisms where
  preserves {A B} φ _ := by
    refine (forget₂Ab.{w} G).epi_of_epi_map ?_
    rw [AddCommGrpCat.epi_iff_surjective]
    exact surjective_smoothFunctionsMap φ.hom ((AddCommGrpCat.epi_iff_surjective _).1 inferInstance)

instance : PreservesFiniteLimits (coind₁.{w} G) :=
  have := (coind₁Adjunction G).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

instance : PreservesFiniteColimits (coind₁.{w} G) :=
  have : (coind₁.{w} G).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have := this.preservesCokernels
  Functor.preservesFiniteColimits_of_preservesCokernels _

lemma injective_coind₁Lift {X : DiscreteModule.{w} G} {A : AddCommGrpCat.{max u w}}
    (φ : X.obj.V ⟶ A) (hφ : Function.Injective φ.hom) :
    Function.Injective (coind₁Lift φ).hom.hom.hom := by
  intro x y h
  apply hφ
  simpa using congr_fun (congrArg Subtype.val h) 1

instance : EnoughInjectives (DiscreteModule.{w} G) where
  presentation X := ⟨{
    J := (coind₁ G).obj (Injective.under X.obj.V)
    injective := Injective.injective_of_adjoint (coind₁Adjunction G) _
    f := coind₁Lift (Injective.ι X.obj.V)
    mono := (forget₂Ab.{w} G).mono_of_mono_map ((AddCommGrpCat.mono_iff_injective _).2
      (injective_coind₁Lift _ ((AddCommGrpCat.mono_iff_injective _).1 inferInstance))) }⟩

instance : HasExt.{max u w} (DiscreteModule.{w} G) :=
  hasExt_of_enoughInjectives _

instance : (forget₂Ab.{w} G).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    have := (forget₂Ab.{w} G).mono_of_mono_map (f := f) inferInstance
    have := (forget₂Ab.{w} G).epi_of_epi_map (f := f) inferInstance
    exact isIso_of_mono_of_epi f

section invariants

variable (M : DiscreteModule.{w} G)

/-- The subgroup of `G`-invariant elements of a discrete `G`-module. -/
def invariantsSubgroup : AddSubgroup M.obj.V where
  carrier := {x | ∀ g, (M.obj.ρ g).asHom.hom x = x}
  zero_mem' := by simp
  add_mem' hx hy g := by simp [hx g, hy g]
  neg_mem' hx g := by simp [hx g]

variable (G) in
/-- The invariants functor `M ↦ Mᴳ` on discrete `G`-modules.
(blueprint: `def-exc-continuous-cohomology`) -/
@[simps obj]
def invariants : DiscreteModule.{w} G ⥤ AddCommGrpCat.{max u w} where
  obj M := AddCommGrpCat.of (invariantsSubgroup M)
  map {M N} f := AddCommGrpCat.ofHom
    ((f.hom.hom.hom.comp (invariantsSubgroup M).subtype).codRestrict _ fun x g ↦ by
      simp [← hom_comm_apply, x.2 g])

variable (G) in
/-- The trivial discrete `G`-module `ℤ`. -/
abbrev intTrivial : DiscreteModule.{w} G :=
  trivial G (AddCommGrpCat.of (ULift.{max u w} ℤ))

/-- Morphisms from `ℤ` to `M` are the invariants of `M`. -/
def homIntTrivialEquiv : (intTrivial G ⟶ M) ≃+ (invariants G).obj M where
  toFun f := ⟨f.hom.hom.hom (ULift.up 1), fun g ↦ by
    rw [← hom_comm_apply]
    rfl⟩
  invFun x := ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom ((zmultiplesHom _ x.1).comp AddEquiv.ulift.toAddMonoidHom)
      comm g := AddCommGrpCat.ext fun n ↦ by
        change n.down • x.1 = (M.obj.ρ g).asHom.hom (n.down • x.1)
        rw [map_zsmul, x.2 g] }
  left_inv f := by
    ext x
    change x.down • f.hom.hom.hom (ULift.up 1) = f.hom.hom.hom x
    rw [← map_zsmul]
    congr 1
    change (x.down • (ULift.up 1 : ULift.{max u w} ℤ)) = x
    exact ULift.ext (by simp)
  right_inv x := by
    refine Subtype.ext ?_
    change (1 : ℤ) • x.1 = x.1
    simp
  map_add' _ _ := rfl

variable (G) in
/-- The continuous cohomology `Hⁿ(G, M) = Extⁿ(ℤ, M)` of a discrete `G`-module: the right
derived functors of the invariants functor (`DiscreteModule.H_zero_addEquiv`), computed in the
derived category of `DiscreteModule G`.
(blueprint: `def-exc-continuous-cohomology`) -/
abbrev H (n : ℕ) : Type (max u w) :=
  Abelian.Ext (intTrivial G) M n

/-- `H⁰(G, M)` is the group of invariants `Mᴳ`. -/
noncomputable def H_zero_addEquiv : H G M 0 ≃+ (invariants G).obj M :=
  Abelian.Ext.addEquiv₀.trans (homIntTrivialEquiv M)

end invariants

end DiscreteModule
