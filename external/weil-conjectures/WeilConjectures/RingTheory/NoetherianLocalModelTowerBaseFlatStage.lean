/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.RingTheory.ColimitEventuallyFlat

/-!
# A base-flat stage in a Noetherian local model tower

Source: Stacks Project, Algebra, Tag 00R6, as applied in the proof of Tag 00R7.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-base-flat-stage).
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

private def ring_diagram
    {I : Type*} [Preorder I] (A : I → Type u) [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (fun i j h ↦ f i j h)] :
    I ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (A i)
  map g := CommRingCat.ofHom (f _ _ (leOfHom g))
  map_id i := by
    ext x
    exact DirectedSystem.map_self' f x
  map_comp g h := by
    ext x
    exact (DirectedSystem.map_map' f (leOfHom g) (leOfHom h) x).symm

private def group_diagram
    {I : Type*} [Preorder I] (N : I → Type t) [∀ i, AddCommGroup (N i)]
    (f : ∀ i j, i ≤ j → N i →+ N j) [DirectedSystem N (fun i j h ↦ f i j h)] :
    I ⥤ AddCommGrpCat.{t} where
  obj i := AddCommGrpCat.of (N i)
  map g := AddCommGrpCat.ofHom (f _ _ (leOfHom g))
  map_id i := by
    ext x
    exact DirectedSystem.map_self' f x
  map_comp g h := by
    ext x
    exact (DirectedSystem.map_map' f (leOfHom g) (leOfHom h) x).symm

private def ring_limit_cocone
    {I : Type*} [Preorder I] (A : I → Type u) [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (fun i j h ↦ f i j h)]
    (R : Type u) [CommRing R] (π : ∀ i, A i →+* R)
    (hπ : ∀ i j h, (π j).comp (f i j h) = π i) : Cocone (ring_diagram A f) where
  pt := CommRingCat.of R
  ι :=
    { app := fun i ↦ CommRingCat.ofHom (π i)
      naturality := fun i j g ↦ by
        ext x
        exact RingHom.congr_fun (hπ i j (leOfHom g)) x }

private noncomputable def ring_limit_isColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (A : I → Type u) [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (fun i j h ↦ f i j h)]
    (R : Type u) [CommRing R] (π : ∀ i, A i →+* R)
    (hπ : ∀ i j h, (π j).comp (f i j h) = π i)
    (hsurj : ∀ r : R, ∃ i, ∃ x : A i, π i x = r)
    (heq : ∀ i (x y : A i), π i x = π i y →
      ∃ j, ∃ h : i ≤ j, f i j h x = f i j h y) :
    IsColimit (ring_limit_cocone A f R π hπ) := by
  let F := ring_diagram A f
  let c := ring_limit_cocone A f R π hπ
  let : HasColimit F := HasColimit.mk
    ⟨_, CommRingCat.FilteredColimits.colimitCoconeIsColimit F⟩
  let : ReflectsColimit F (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨i, y, hy.symm⟩
  · intro i x y h
    obtain ⟨j, hij, hxy⟩ := heq i x y h
    exact ⟨j, homOfLE hij, hxy⟩

private def group_limit_cocone
    {I : Type*} [Preorder I] (N : I → Type t) [∀ i, AddCommGroup (N i)]
    (f : ∀ i j, i ≤ j → N i →+ N j) [DirectedSystem N (fun i j h ↦ f i j h)]
    (M : Type t) [AddCommGroup M] (ν : ∀ i, N i →+ M)
    (hν : ∀ i j h, (ν j).comp (f i j h) = ν i) : Cocone (group_diagram N f) where
  pt := AddCommGrpCat.of M
  ι :=
    { app := fun i ↦ AddCommGrpCat.ofHom (ν i)
      naturality := fun i j g ↦ by
        ext x
        exact DFunLike.congr_fun (hν i j (leOfHom g)) x }

private noncomputable def group_limit_isColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (N : I → Type (max u t)) [∀ i, AddCommGroup (N i)]
    (f : ∀ i j, i ≤ j → N i →+ N j) [DirectedSystem N (fun i j h ↦ f i j h)]
    (M : Type (max u t)) [AddCommGroup M] (ν : ∀ i, N i →+ M)
    (hν : ∀ i j h, (ν j).comp (f i j h) = ν i)
    (hsurj : ∀ m : M, ∃ i, ∃ x : N i, ν i x = m)
    (heq : ∀ i (x y : N i), ν i x = ν i y →
      ∃ j, ∃ h : i ≤ j, f i j h x = f i j h y) :
    IsColimit (group_limit_cocone N f M ν hν) := by
  let F := group_diagram N f
  let : HasColimit F := HasColimit.mk
    ⟨_, AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit F⟩
  let : PreservesColimit F (forget AddCommGrpCat) :=
    preservesColimit_of_preserves_colimit_cocone
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit F)
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget AddCommGrpCat))
  let : ReflectsColimit F (forget AddCommGrpCat) :=
    reflectsColimit_of_reflectsIsomorphisms F (forget AddCommGrpCat)
  apply isColimitOfReflects (forget AddCommGrpCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨i, y, hy.symm⟩
  · intro i x y h
    obtain ⟨j, hij, hxy⟩ := heq i x y h
    exact ⟨j, homOfLE hij, hxy⟩

/-- A flat limit module has a base-flat stage.
Source: Stacks Project, Algebra, Tag 00R6, as applied in the proof of Tag 00R7.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-base-flat-stage).

Proof:
1. Convert the base and top ring directed systems and the module directed system to
   functors on the index preorder. The directed-system axioms give identity and composition.
   The compatible ring and module limit maps give cocones, after lifting limit rings to
   the stage-ring universe as needed.
2. The elementwise representation and eventual-equality fields of the tower imply these
   cocones are colimits: every element is represented; two representatives are equal
   exactly when their images agree at a common later stage. The universal maps from these
   colimits are therefore bijective ring or additive homomorphisms. Semilinearity and
   the ring-map squares transport scalar structures and base flatness to the colimits.
3. Apply `RingTheory.exists_flat_stage`. All stage rings are Noetherian local, all ring
   maps are local, the stage modules are finite and the module transitions are semilinear.
   The fields `baseTransition` and `moduleTransition` give precisely its localization
   and module tensor-isomorphism hypotheses. Transport the resulting flat stage from
   the restricted action along the base-to-top map to the tower's specified base action;
   these actions agree by the two stage scalar towers. No persistence or fibre argument
   is part of this statement, and the zero module is allowed.
-/
theorem NoetherianLocalModelTower.exists_baseFlat_stage
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    (X : NoetherianLocalModelTower R S S' M) [Module.Flat R M] :
    letI := X.commR
    letI := X.addN
    letI := X.moduleR
    ∃ i : X.ι, Module.Flat (X.R₀ i) (X.N₀ i) := by
  classical
  let := X.preorder
  let := X.nonempty
  let := X.directed
  let := X.commR
  let := X.commS
  let := X.commT
  let := X.localR
  let := X.localT
  let := X.noethR
  let := X.noethT
  let := X.algRS
  let := X.algST
  let := X.algRT
  let := X.towerRST
  let := X.addN
  let := X.moduleR
  let := X.moduleS
  let := X.moduleT
  let := X.towerSTN
  let := X.towerRSN
  let := X.finite
  let := X.algRLimit
  let := X.algSLimit
  let := X.algTLimit
  let := X.rSystem
  let := X.tSystem
  let := X.nSystem
  let A := ring_diagram X.R₀ X.rmap
  let B := ring_diagram X.T₀ X.tmap
  let : ∀ i, IsLocalRing (A.obj i) := X.localR
  let : ∀ i, IsLocalRing (B.obj i) := X.localT
  let : ∀ i, IsNoetherianRing (A.obj i) := X.noethR
  let : ∀ i, IsNoetherianRing (B.obj i) := X.noethT
  let π : ∀ i, X.R₀ i →+* ULift.{max u v w} R :=
    fun i ↦ ULift.ringEquiv.symm.toRingHom.comp (algebraMap (X.R₀ i) R)
  let κ : ∀ i, X.T₀ i →+* ULift.{max u v w} S' :=
    fun i ↦ ULift.ringEquiv.symm.toRingHom.comp (algebraMap (X.T₀ i) S')
  have hπ : ∀ i j h, (π j).comp (X.rmap i j h) = π i := by
    intro i j h
    exact congrArg (fun f ↦ ULift.ringEquiv.symm.toRingHom.comp f)
      (X.rlimit_comm i j h)
  have hκ : ∀ i j h, (κ j).comp (X.tmap i j h) = κ i := by
    intro i j h
    exact congrArg (fun f ↦ ULift.ringEquiv.symm.toRingHom.comp f)
      (X.tlimit_comm i j h)
  let cA := ring_limit_cocone X.R₀ X.rmap (ULift.{max u v w} R) π hπ
  let cB := ring_limit_cocone X.T₀ X.tmap (ULift.{max u v w} S') κ hκ
  have hcA : IsColimit cA := ring_limit_isColimit X.R₀ X.rmap _ π hπ
    (fun r ↦ by
      obtain ⟨i, x, hx⟩ := X.rlimit_surj r.down
      exact ⟨i, x, congrArg ULift.up hx⟩)
    (fun i x y h ↦ X.rlimit_eq i x y (congrArg ULift.down h))
  have hcB : IsColimit cB := ring_limit_isColimit X.T₀ X.tmap _ κ hκ
    (fun s ↦ by
      obtain ⟨i, x, hx⟩ := X.tlimit_surj s.down
      exact ⟨i, x, congrArg ULift.up hx⟩)
    (fun i x y h ↦ X.tlimit_eq i x y (congrArg ULift.down h))
  let : HasColimit A := HasColimit.mk ⟨cA, hcA⟩
  let : HasColimit B := HasColimit.mk ⟨cB, hcB⟩
  let eR : (colimit A : CommRingCat) ≃+* R :=
    (colimit.isoColimitCocone ⟨cA, hcA⟩).commRingCatIsoToRingEquiv.trans
      ULift.ringEquiv
  let eT : (colimit B : CommRingCat) ≃+* S' :=
    (colimit.isoColimitCocone ⟨cB, hcB⟩).commRingCatIsoToRingEquiv.trans
      ULift.ringEquiv
  have heR (i : X.ι) (r : X.R₀ i) : eR ((colimit.ι A i).hom r) =
      algebraMap (X.R₀ i) R r := by
    exact congrArg ULift.down (ConcreteCategory.congr_hom
      (colimit.isoColimitCocone_ι_hom ⟨cA, hcA⟩ i) r)
  have heT (i : X.ι) (s : X.T₀ i) : eT ((colimit.ι B i).hom s) =
      algebraMap (X.T₀ i) S' s := by
    exact congrArg ULift.down (ConcreteCategory.congr_hom
      (colimit.isoColimitCocone_ι_hom ⟨cB, hcB⟩ i) s)
  let N : X.ι → Type (max u v w t) := fun i ↦ ULift.{max u v w} (X.N₀ i)
  let nmap : ∀ i j, i ≤ j → N i →+ N j := fun i j h ↦
    AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((X.nmap i j h).comp AddEquiv.ulift.toAddMonoidHom)
  let : DirectedSystem N (fun i j h ↦ nmap i j h) :=
    { map_self {i} x := by
        apply ULift.ext
        exact DirectedSystem.map_self' X.nmap x.down
      map_map {k j i} hij hjk x := by
        apply ULift.ext
        exact DirectedSystem.map_map' X.nmap hij hjk x.down }
  let D := group_diagram N nmap
  let : ∀ i, Module (B.obj i) (D.obj i) := fun i ↦
    (inferInstance : Module (X.T₀ i) (ULift.{max u v w} (X.N₀ i)))
  let : ∀ i, Module.Finite (B.obj i) (D.obj i) := fun i ↦
    (inferInstance : Module.Finite (X.T₀ i) (ULift.{max u v w} (X.N₀ i)))
  let ν : ∀ i, N i →+ ULift.{max u v w} M := fun i ↦
    AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((X.nlimit i).comp AddEquiv.ulift.toAddMonoidHom)
  have hν : ∀ i j h, (ν j).comp (nmap i j h) = ν i := by
    intro i j h
    apply AddMonoidHom.ext
    intro x
    apply ULift.ext
    exact DFunLike.congr_fun (X.nlimit_comm i j h) x.down
  let cD := group_limit_cocone N nmap (ULift.{max u v w} M) ν hν
  have hcD : IsColimit cD := group_limit_isColimit.{max u v w, t} N nmap _ ν hν
    (fun m ↦ by
      obtain ⟨i, x, hx⟩ := X.nlimit_surj m.down
      exact ⟨i, ULift.up x, congrArg ULift.up hx⟩)
    (fun i x y h ↦ by
      obtain ⟨j, hij, hxy⟩ := X.nlimit_eq i x.down y.down (congrArg ULift.down h)
      exact ⟨j, hij, congrArg ULift.up hxy⟩)
  let : HasColimit D := HasColimit.mk ⟨cD, hcD⟩
  let eN : (colimit D : AddCommGrpCat) ≃+ M :=
    (colimit.isoColimitCocone ⟨cD, hcD⟩).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift
  have heN (i : X.ι) (x : N i) : eN ((colimit.ι D i).hom x) = X.nlimit i x.down := by
    exact congrArg ULift.down (ConcreteCategory.congr_hom
      (colimit.isoColimitCocone_ι_hom ⟨cD, hcD⟩ i) x)
  have hrtcomm (i j : X.ι) (h : i ≤ j) :
      (X.tmap i j h).comp (algebraMap (X.R₀ i) (X.T₀ i)) =
        (algebraMap (X.R₀ j) (X.T₀ j)).comp (X.rmap i j h) := by
    rw [IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i),
      ← RingHom.comp_assoc, X.st_comm, RingHom.comp_assoc, X.rs_comm,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq (X.R₀ j) (X.S₀ j) (X.T₀ j)]
  have hrtlim (i : X.ι) :
      (algebraMap (X.T₀ i) S').comp (algebraMap (X.R₀ i) (X.T₀ i)) =
        (algebraMap R S').comp (algebraMap (X.R₀ i) R) := by
    rw [IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i),
      ← RingHom.comp_assoc, X.st_limit_comm, RingHom.comp_assoc, X.rs_limit_comm,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R S S']
  let φ : ∀ i, A.obj i →+* B.obj i := fun i ↦ algebraMap (X.R₀ i) (X.T₀ i)
  let ψ := eT.symm.toRingHom.comp ((algebraMap R S').comp eR.toRingHom)
  have hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i) := by
    intro i
    ext r
    apply eT.injective
    change eT (eT.symm (algebraMap R S' (eR ((colimit.ι A i).hom r)))) =
      eT ((colimit.ι B i).hom (φ i r))
    rw [eT.apply_symm_apply, heR, heT]
    exact (RingHom.congr_fun (hrtlim i) r).symm
  let : Module (colimit B : CommRingCat) M := Module.compHom M eT.toRingHom
  let : Module (colimit B : CommRingCat) (colimit D : AddCommGrpCat) :=
    eN.module (colimit B : CommRingCat)
  have hlimitScalar : ∀ (i : X.ι) (b : B.obj i) (x : D.obj i),
      (colimit.ι D i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι D i).hom x := by
    intro i b x
    apply eN.injective
    change eN ((colimit.ι D i).hom (b • x)) =
      eN (eN.symm (eT ((colimit.ι B i).hom b) • eN ((colimit.ι D i).hom x)))
    rw [eN.apply_symm_apply, heN, heN, heT]
    exact X.nlimit_smul i b x.down
  have : IsScalarTower R S' M := IsScalarTower.to₁₃₄ R S S' M
  have hflat : letI := Module.compHom (colimit D : AddCommGrpCat) ψ
      Module.Flat (colimit A : CommRingCat) (colimit D : AddCommGrpCat) := by
    let : Algebra (colimit A : CommRingCat) R := eR.toRingHom.toAlgebra
    let : Module (colimit A : CommRingCat) M := Module.compHom M eR.toRingHom
    have : IsScalarTower (colimit A : CommRingCat) R M := IsScalarTower.of_compHom _ _ _
    have : Module.Flat (colimit A : CommRingCat) R :=
      (RingHom.flat_algebraMap_iff).mp (RingHom.Flat.of_bijective eR.bijective)
    have : Module.Flat (colimit A : CommRingCat) M := Module.Flat.trans _ R M
    let : Module (colimit A : CommRingCat) (colimit D : AddCommGrpCat) :=
      Module.compHom (colimit D : AddCommGrpCat) ψ
    let en : (colimit D : AddCommGrpCat) ≃ₗ[(colimit A : CommRingCat)] M :=
      { toAddEquiv := eN
        map_smul' := by
          intro r x
          change eN (eN.symm (eT (ψ r) • eN x)) = eR r • eN x
          rw [eN.apply_symm_apply]
          change eT (eT.symm (algebraMap R S' (eR r))) • eN x = eR r • eN x
          rw [eT.apply_symm_apply, algebraMap_smul] }
    exact Module.Flat.of_linearEquiv en
  have hφ : ∀ i, IsLocalHom (φ i) := by
    intro i
    dsimp only [φ, A, B, ring_diagram]
    rw [IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i)]
    let := X.localRS i
    let := X.localST i
    infer_instance
  have hscalar : ∀ (i j : X.ι) (g : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map g).hom (b • x) = (B.map g).hom b • (D.map g).hom x := by
    intro i j g b x
    apply ULift.ext
    exact X.nmap_smul i j (leOfHom g) b x.down
  have hloc : ∀ (i j : X.ι) (g : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (A.map g).hom.toAlgebra
      ∃ (q : B.obj i ⊗[A.obj i] A.obj j →+* B.obj j)
        (U : Submonoid (B.obj i ⊗[A.obj i] A.obj j)),
        (∀ (b : B.obj i) (a : A.obj j),
          q (b ⊗ₜ[A.obj i] a) = (B.map g).hom b * φ j a) ∧
        (letI := q.toAlgebra; IsLocalization U (B.obj j)) := by
    intro i j g
    have hAlg : (φ i).toAlgebra = X.algRT i := by
      change (algebraMap (X.R₀ i) (X.T₀ i)).toAlgebra = X.algRT i
      exact toAlgebra_algebraMap
    rw [hAlg]
    exact X.baseTransition i j (leOfHom g)
  have hbase : ∀ (i j : X.ι) (g : i ⟶ j),
      letI := (B.map g).hom.toAlgebra
      ∃ e : (B.obj j ⊗[B.obj i] D.obj i) ≃ₗ[B.obj j] D.obj j,
        ∀ (b : B.obj j) (x : D.obj i), e (b ⊗ₜ[B.obj i] x) = b • (D.map g).hom x := by
    intro i j g
    change letI := (X.tmap i j (leOfHom g)).toAlgebra
      ∃ e : (X.T₀ j ⊗[X.T₀ i] N i) ≃ₗ[X.T₀ j] N j,
        ∀ (b : X.T₀ j) (x : N i), e (b ⊗ₜ[X.T₀ i] x) = b • nmap i j (leOfHom g) x
    let : Algebra (X.T₀ i) (X.T₀ j) := (X.tmap i j (leOfHom g)).toAlgebra
    obtain ⟨e, he⟩ := X.moduleTransition i j (leOfHom g)
    let e' := TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (X.T₀ j) (X.T₀ j)) (ULift.moduleEquiv (R := X.T₀ i) (M := X.N₀ i))
    refine ⟨e'.trans (e.trans (ULift.moduleEquiv (R := X.T₀ j) (M := X.N₀ j)).symm), ?_⟩
    intro b x
    apply ULift.ext
    exact he b x.down
  obtain ⟨i, hi⟩ := RingTheory.exists_flat_stage A B D φ hφ
    (fun i j g ↦ X.rmap_local i j (leOfHom g))
    (fun i j g ↦ X.tmap_local i j (leOfHom g))
    (fun i j g ↦ hrtcomm i j (leOfHom g)) hscalar ψ hψ hlimitScalar hloc hbase hflat
  refine ⟨i, ?_⟩
  dsimp only [φ, A, B, D, ring_diagram, group_diagram] at hi
  have : IsScalarTower (X.R₀ i) (X.T₀ i) (X.N₀ i) :=
    IsScalarTower.to₁₃₄ (X.R₀ i) (X.S₀ i) (X.T₀ i) (X.N₀ i)
  let : Module (X.R₀ i) (N i) :=
    Module.compHom (N i) (algebraMap (X.R₀ i) (X.T₀ i))
  have : Module.Flat (X.R₀ i) (N i) := hi
  let ec : X.N₀ i ≃ₗ[X.R₀ i] N i :=
    { toAddEquiv := AddEquiv.ulift.symm
      map_smul' := by
        intro r x
        apply ULift.ext
        exact (algebraMap_smul (X.T₀ i) r x).symm }
  exact Module.Flat.of_linearEquiv ec

end Module
