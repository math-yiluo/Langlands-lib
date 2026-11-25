/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # Explicit closed-fibre systems of a Noetherian local model tower

Source: Stacks Project, Algebra, Tag 00R7, the quotient systems in its proof.
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module.NoetherianLocalModelTower

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
  [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup M]
  [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
  (X : Module.NoetherianLocalModelTower R S S' M)

attribute [local instance] Module.NoetherianLocalModelTower.preorder
  Module.NoetherianLocalModelTower.commR Module.NoetherianLocalModelTower.commS
  Module.NoetherianLocalModelTower.commT Module.NoetherianLocalModelTower.localR
  Module.NoetherianLocalModelTower.algRS Module.NoetherianLocalModelTower.algST
  Module.NoetherianLocalModelTower.algRT Module.NoetherianLocalModelTower.towerRST
  Module.NoetherianLocalModelTower.addN Module.NoetherianLocalModelTower.moduleT
  Module.NoetherianLocalModelTower.moduleS Module.NoetherianLocalModelTower.towerSTN

/-- The extended maximal ideal in the middle ring. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberIdealS (i : X.ι) : Ideal (X.S₀ i) :=
  Ideal.map (algebraMap (X.R₀ i) (X.S₀ i)) (IsLocalRing.maximalIdeal (X.R₀ i))

/-- The extended maximal ideal in the top ring. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberIdealT (i : X.ι) : Ideal (X.T₀ i) :=
  Ideal.map (algebraMap (X.R₀ i) (X.T₀ i)) (IsLocalRing.maximalIdeal (X.R₀ i))

/-- The middle closed fibre. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
abbrev FiberS (i : X.ι) := X.S₀ i ⧸ X.fiberIdealS i

/-- The top closed fibre. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
abbrev FiberT (i : X.ι) := X.T₀ i ⧸ X.fiberIdealT i

/-- The finite module's closed fibre, before its universe lift. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
abbrev FiberN (i : X.ι) := X.FiberT i ⊗[X.T₀ i] X.N₀ i

/-- A commuting local square preserves the extended maximal ideals. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem map_fiberIdeal_le
    {R₁ R₂ A₁ A₂ : Type*} [CommRing R₁] [CommRing R₂]
    [CommRing A₁] [CommRing A₂] [IsLocalRing R₁] [IsLocalRing R₂]
    (r : R₁ →+* R₂) [IsLocalHom r] (a : A₁ →+* A₂)
    (p : R₁ →+* A₁) (q : R₂ →+* A₂) (h : a.comp p = q.comp r) :
    Ideal.map a (Ideal.map p (IsLocalRing.maximalIdeal R₁)) ≤
      Ideal.map q (IsLocalRing.maximalIdeal R₂) := by
  rw [Ideal.map_map, h, ← Ideal.map_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le r)

/-- The quotient transition of the middle rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberSMap (i j : X.ι) (h : i ≤ j) : X.FiberS i →+* X.FiberS j :=
  Ideal.quotientMap _ (X.smap i j h) (by
    let := X.rmap_local i j h
    exact Ideal.map_le_iff_le_comap.mp
      (map_fiberIdeal_le (X.rmap i j h) (X.smap i j h) _ _ (X.rs_comm i j h)))

/-- The R-to-T transition square, derived from the two tower squares. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem rt_comm (i j : X.ι) (h : i ≤ j) :
    (X.tmap i j h).comp (algebraMap (X.R₀ i) (X.T₀ i)) =
      (algebraMap (X.R₀ j) (X.T₀ j)).comp (X.rmap i j h) := by
  rw [IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i),
    IsScalarTower.algebraMap_eq (X.R₀ j) (X.S₀ j) (X.T₀ j)]
  rw [← RingHom.comp_assoc, X.st_comm i j h, RingHom.comp_assoc,
    X.rs_comm i j h, ← RingHom.comp_assoc]

/-- The quotient transition of the top rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberTMap (i j : X.ι) (h : i ≤ j) : X.FiberT i →+* X.FiberT j :=
  Ideal.quotientMap _ (X.tmap i j h) (by
    let := X.rmap_local i j h
    exact Ideal.map_le_iff_le_comap.mp
      (map_fiberIdeal_le (X.rmap i j h) (X.tmap i j h) _ _ (X.rt_comm i j h)))

/-- The quotient of the middle-to-top ring map. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberφ (i : X.ι) : X.FiberS i →+* X.FiberT i :=
  Ideal.quotientMap _ (algebraMap (X.S₀ i) (X.T₀ i)) (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [fiberIdealS, fiberIdealT, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i)]
    )

/-- The functor of middle closed-fibre rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
@[reducible]
def fiberA : X.ι ⥤ CommRingCat.{max u v w} where
  obj i := CommRingCat.of (X.FiberS i)
  map {i j} f := CommRingCat.ofHom (X.fiberSMap i j (leOfHom f))
  map_id i := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    simpa [fiberSMap] using congrArg (Ideal.Quotient.mk (X.fiberIdealS i))
      (X.sSystem.map_self x)
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    simpa [fiberSMap] using congrArg (Ideal.Quotient.mk (X.fiberIdealS k))
      (X.sSystem.map_map (leOfHom f) (leOfHom g) x).symm

/-- The functor of top closed-fibre rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
@[reducible]
def fiberB : X.ι ⥤ CommRingCat.{max u v w} where
  obj i := CommRingCat.of (X.FiberT i)
  map {i j} f := CommRingCat.ofHom (X.fiberTMap i j (leOfHom f))
  map_id i := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    simpa [fiberTMap] using congrArg (Ideal.Quotient.mk (X.fiberIdealT i))
      (X.tSystem.map_self x)
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    simpa [fiberTMap] using congrArg (Ideal.Quotient.mk (X.fiberIdealT k))
      (X.tSystem.map_map (leOfHom f) (leOfHom g) x).symm

/-- The quotient ring transition as a semilinear map over the top transition. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberTLinear (i j : X.ι) (h : i ≤ j) :
    X.FiberT i →ₛₗ[X.tmap i j h] X.FiberT j where
  __ := (X.fiberTMap i j h).toAddMonoidHom
  map_smul' a b := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp [Algebra.smul_def, fiberTMap]

/-- The module transition as a semilinear map. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberNLinear (i j : X.ι) (h : i ≤ j) :
    X.N₀ i →ₛₗ[X.tmap i j h] X.N₀ j where
  __ := X.nmap i j h
  map_smul' := X.nmap_smul i j h

/-- The closed-fibre tensor transition. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberNMap (i j : X.ι) (h : i ≤ j) : X.FiberN i →+ X.FiberN j :=
  (TensorProduct.map (X.fiberTLinear i j h) (X.fiberNLinear i j h)).toAddMonoidHom

/-- (blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system) -/
@[simp]
theorem fiberNMap_tmul (i j : X.ι) (h : i ≤ j) (b : X.FiberT i) (n : X.N₀ i) :
    X.fiberNMap i j h (b ⊗ₜ n) = X.fiberTMap i j h b ⊗ₜ X.nmap i j h n := rfl

/-- The identity law of the closed-fibre tensor transitions. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberNMap_self (i : X.ι) (x : X.FiberN i) : X.fiberNMap i i le_rfl x = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul b n =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp [fiberTMap, X.tSystem.map_self, X.nSystem.map_self]

/-- The composition law of the closed-fibre tensor transitions. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberNMap_comp (i j k : X.ι) (h : i ≤ j) (h' : j ≤ k) (x : X.FiberN i) :
    X.fiberNMap j k h' (X.fiberNMap i j h x) = X.fiberNMap i k (h.trans h') x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul b n =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp [fiberTMap, X.tSystem.map_map h h', X.nSystem.map_map h h']

/-- The universe lift of a closed-fibre module transition. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberDMap (i j : X.ι) (h : i ≤ j) :
    ULift.{max u v w t} (X.FiberN i) →+ ULift.{max u v w t} (X.FiberN j) :=
  ((ULift.moduleEquiv (R := X.T₀ j)).toAddEquiv.symm.toAddMonoidHom.comp (X.fiberNMap i j h)).comp
    (ULift.moduleEquiv (R := X.T₀ i)).toAddEquiv.toAddMonoidHom

/-- The actual closed-fibre additive-group diagram, with its required universe. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
@[reducible]
def fiberD : X.ι ⥤ AddCommGrpCat.{max u v w t} where
  obj i := AddCommGrpCat.of (ULift.{max u v w t} (X.FiberN i))
  map {i j} f := AddCommGrpCat.ofHom (X.fiberDMap i j (leOfHom f))
  map_id i := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact X.fiberNMap_self i x.down
  map_comp {i j k} f g := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact (X.fiberNMap_comp i j k (leOfHom f) (leOfHom g) x.down).symm

/-- The actual stage action on the lifted tensor product. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
@[instance_reducible]
def fiberAct (i : X.ι) : Module (X.fiberB.obj i) (X.fiberD.obj i) := by
  change Module (X.FiberT i) (ULift.{max u v w t} (X.FiberN i))
  infer_instance

/-- The quotient middle-to-top maps form a natural transformation. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
def fiberφNat : X.fiberA ⟶ X.fiberB where
  app i := CommRingCat.ofHom (X.fiberφ i)
  naturality i j f := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    simpa [fiberA, fiberB, fiberφ, fiberSMap, fiberTMap] using
      congrArg (Ideal.Quotient.mk (X.fiberIdealT j))
        (RingHom.congr_fun (X.st_comm i j (leOfHom f)) x).symm

/-- The actual colimit ring map induced by the quotient natural transformation. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
noncomputable def fiberψ :
    (colimit X.fiberA : CommRingCat.{max u v w}) →+*
      (colimit X.fiberB : CommRingCat.{max u v w}) :=
  (colimMap X.fiberφNat).hom

/-- The colimit ring map commutes with the coprojections. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberψ_comp_ι (i : X.ι) :
    X.fiberψ.comp (colimit.ι X.fiberA i).hom =
      (colimit.ι X.fiberB i).hom.comp (X.fiberφ i) := by
  exact congrArg CommRingCat.Hom.hom (ι_colimMap X.fiberφNat i)

/-- Extended maximal ideals are proper in the middle stage rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberIdealS_ne_top (i : X.ι) : X.fiberIdealS i ≠ ⊤ := by
  let := X.localS i
  let := X.localRS i
  exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap (X.R₀ i) (X.S₀ i))).ne

/-- Extended maximal ideals are proper in the top stage rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberIdealT_ne_top (i : X.ι) : X.fiberIdealT i ≠ ⊤ := by
  let := X.localT i
  let := X.localRS i
  let := X.localST i
  have : IsLocalHom (algebraMap (X.R₀ i) (X.T₀ i)) := by
    rw [IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i)]
    infer_instance
  exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap (X.R₀ i) (X.T₀ i))).ne

/-- The middle closed fibres are local rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberA_local (i : X.ι) : IsLocalRing (X.fiberA.obj i) := by
  change IsLocalRing (X.FiberS i)
  let := X.localS i
  let := Ideal.Quotient.nontrivial_iff.mpr (X.fiberIdealS_ne_top i)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The top closed fibres are local rings. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberB_local (i : X.ι) : IsLocalRing (X.fiberB.obj i) := by
  change IsLocalRing (X.FiberT i)
  let := X.localT i
  let := Ideal.Quotient.nontrivial_iff.mpr (X.fiberIdealT_ne_top i)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The middle closed fibres are Noetherian. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberA_noetherian (i : X.ι) : IsNoetherianRing (X.fiberA.obj i) := by
  let := X.noethS i
  change IsNoetherianRing (X.FiberS i)
  infer_instance

/-- The top closed fibres are Noetherian. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberB_noetherian (i : X.ι) : IsNoetherianRing (X.fiberB.obj i) := by
  let := X.noethT i
  change IsNoetherianRing (X.FiberT i)
  infer_instance

/-- The lifted tensor modules are finite over the top closed fibres. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberD_finite (i : X.ι) :
    letI := X.fiberAct i
    Module.Finite (X.fiberB.obj i) (X.fiberD.obj i) := by
  let := X.finite i
  change Module.Finite (X.FiberT i) (ULift.{max u v w t} (X.FiberN i))
  infer_instance

/-- Quotient transitions induced by local homomorphisms are local. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem quotientMap_local
    {A₁ A₂ : Type*} [CommRing A₁] [CommRing A₂] [IsLocalRing A₂]
    {I : Ideal A₁} {J : Ideal A₂} [Nontrivial (A₂ ⧸ J)]
    (f : A₁ →+* A₂) [IsLocalHom f] (h : I ≤ J.comap f) :
    IsLocalHom (Ideal.quotientMap J f h) := by
  let := IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  constructor
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk] at ha
  exact (Ideal.Quotient.mk I).isUnit_map
    (isUnit_of_map_unit f a (isUnit_of_map_unit (Ideal.Quotient.mk J) (f a) ha))

/-- The stage maps between the closed-fibre rings are local. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberφ_local (i : X.ι) : IsLocalHom (X.fiberφ i) := by
  let := X.localT i
  let := X.localST i
  let := Ideal.Quotient.nontrivial_iff.mpr (X.fiberIdealT_ne_top i)
  exact quotientMap_local _ _

/-- The middle closed-fibre ring transitions are local. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberA_map_local (i j : X.ι) (f : i ⟶ j) :
    IsLocalHom (X.fiberA.map f).hom := by
  let := X.localS j
  let := X.smap_local i j (leOfHom f)
  let := Ideal.Quotient.nontrivial_iff.mpr (X.fiberIdealS_ne_top j)
  change IsLocalHom (X.fiberSMap i j (leOfHom f))
  unfold fiberSMap
  apply quotientMap_local

/-- The top closed-fibre ring transitions are local. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberB_map_local (i j : X.ι) (f : i ⟶ j) :
    IsLocalHom (X.fiberB.map f).hom := by
  let := X.localT j
  let := X.tmap_local i j (leOfHom f)
  let := Ideal.Quotient.nontrivial_iff.mpr (X.fiberIdealT_ne_top j)
  change IsLocalHom (X.fiberTMap i j (leOfHom f))
  unfold fiberTMap
  apply quotientMap_local

/-- Commutativity of the quotient transition squares. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiber_square (i j : X.ι) (f : i ⟶ j) :
    (X.fiberB.map f).hom.comp (X.fiberφ i) =
      (X.fiberφ j).comp (X.fiberA.map f).hom := by
  exact congrArg CommRingCat.Hom.hom (X.fiberφNat.naturality f).symm

/-- The closed-fibre tensor transitions respect the quotient-ring scalar actions. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberNMap_smul (i j : X.ι) (h : i ≤ j) (b : X.FiberT i) (x : X.FiberN i) :
    X.fiberNMap i j h (b • x) = X.fiberTMap i j h b • X.fiberNMap i j h x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul c n =>
    simp only [TensorProduct.smul_tmul', fiberNMap_tmul, smul_eq_mul, map_mul]

/-- Semilinearity of the lifted closed-fibre module transitions. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberD_map_smul (i j : X.ι) (f : i ⟶ j)
    (b : X.fiberB.obj i) (x : X.fiberD.obj i) :
    letI := X.fiberAct
    (X.fiberD.map f).hom (b • x) =
      (X.fiberB.map f).hom b • (X.fiberD.map f).hom x := by
  apply ULift.ext
  exact X.fiberNMap_smul i j (leOfHom f) b x.down

/-- Restricting the top extended-ideal submodule gives the middle extended-ideal submodule. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiber_submodule_eq (i : X.ι) :
    (X.fiberIdealT i • (⊤ : Submodule (X.T₀ i) (X.N₀ i))).restrictScalars (X.S₀ i) =
      X.fiberIdealS i • (⊤ : Submodule (X.S₀ i) (X.N₀ i)) := by
  have h : X.fiberIdealT i = (X.fiberIdealS i).map
      (algebraMap (X.S₀ i) (X.T₀ i)) := by
    rw [fiberIdealS, fiberIdealT, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [h, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

/-- The two tensor descriptions of the stage closed-fibre module agree. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
noncomputable def fiberNEquiv (i : X.ι) :
    X.FiberN i ≃ₗ[X.S₀ i] (X.FiberS i ⊗[X.S₀ i] X.N₀ i) :=
  ((TensorProduct.quotTensorEquivQuotSMul (X.N₀ i) (X.fiberIdealT i)).restrictScalars
    (X.S₀ i)).trans
    ((Submodule.Quotient.restrictScalarsEquiv (X.S₀ i)
      (X.fiberIdealT i • (⊤ : Submodule (X.T₀ i) (X.N₀ i)))).symm.trans
      ((Submodule.quotEquivOfEq _ _ (X.fiber_submodule_eq i)).trans
        (TensorProduct.quotTensorEquivQuotSMul (X.N₀ i) (X.fiberIdealS i)).symm))

/-- The additive stage comparison, including the explicit universe lift. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
noncomputable def fiberDEquiv (i : X.ι) :
    X.fiberD.obj i ≃+ (X.FiberS i ⊗[X.S₀ i] X.N₀ i) :=
  (ULift.moduleEquiv (R := X.S₀ i)).toAddEquiv.trans (X.fiberNEquiv i).toAddEquiv

/-- Scalar compatibility of the stage comparison. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiberDEquiv_smul (i : X.ι) (a : X.fiberA.obj i) (x : X.fiberD.obj i) :
    letI := X.fiberAct
    letI := Module.compHom (X.fiberD.obj i) (X.fiberφ i)
    X.fiberDEquiv i (a • x) = a • X.fiberDEquiv i x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change X.fiberNEquiv i
      ((Ideal.Quotient.mk (X.fiberIdealT i) (algebraMap (X.S₀ i) (X.T₀ i) a)) • x.down) = _
  simp [fiberDEquiv, ← Ideal.Quotient.algebraMap_eq]

/-- Closed-fibre module transitions are scalar-extension equivalences. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-system)
-/
theorem fiber_module_baseChange (i j : X.ι) (f : i ⟶ j) :
    letI := X.fiberAct
    letI := (X.fiberB.map f).hom.toAlgebra
    ∃ e : (X.fiberB.obj j ⊗[X.fiberB.obj i] X.fiberD.obj i) ≃ₗ[X.fiberB.obj j]
      X.fiberD.obj j,
      ∀ (b : X.fiberB.obj j) (x : X.fiberD.obj i),
        e (b ⊗ₜ x) = b • (X.fiberD.map f).hom x := by
  let := X.fiberAct
  let := (X.fiberB.map f).hom.toAlgebra
  let : Algebra (X.T₀ i) (X.T₀ j) := (X.tmap i j (leOfHom f)).toAlgebra
  have : IsScalarTower (X.T₀ i) (X.FiberT i) (X.FiberT j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  obtain ⟨e, he⟩ := X.moduleTransition i j (leOfHom f)
  let e₁ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.FiberT j) (X.FiberT j))
    (ULift.moduleEquiv (R := X.FiberT i) (M := X.FiberN i))
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
    (X.T₀ i) (X.FiberT i) (X.FiberT j) (X.FiberT j) (X.N₀ i)
  let e₃ := (TensorProduct.AlgebraTensorModule.cancelBaseChange
    (X.T₀ i) (X.T₀ j) (X.FiberT j) (X.FiberT j) (X.N₀ i)).symm
  let e₄ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.FiberT j) (X.FiberT j)) e
  let e₅ := (ULift.moduleEquiv (R := X.FiberT j) (M := X.FiberN j)).symm
  refine ⟨e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))), ?_⟩
  intro b x
  change ULift.up (e₄ (e₃ (e₂ (b ⊗ₜ x.down)))) = _
  apply ULift.ext
  change e₄ (e₃ (e₂ (b ⊗ₜ x.down))) = b • X.fiberNMap i j (leOfHom f) x.down
  induction x.down using TensorProduct.inductionOn with
  | add x y hx hy => simp [TensorProduct.tmul_add, smul_add, hx, hy]
  | tmul c n =>
    simp [e₂, e₃, e₄, he, Algebra.smul_def, TensorProduct.smul_tmul',
      smul_eq_mul, mul_comm]
    rfl

end Module.NoetherianLocalModelTower
