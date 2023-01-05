// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

#![allow(dead_code)]
#![allow(unused_must_use)]
#![allow(unused_imports)]

use move_binary_format::{
    errors::VMResult,
    file_format::{
        AbilitySet, AddressIdentifierIndex, Bytecode, Bytecode::*, CodeUnit, CompiledModule,
        Constant, ConstantPoolIndex, FieldDefinition, FunctionDefinition, FunctionHandle,
        FunctionHandleIndex, FunctionInstantiation, FunctionInstantiationIndex, IdentifierIndex,
        ModuleHandle, ModuleHandleIndex, Signature, SignatureIndex, SignatureToken,
        SignatureToken::*, StructDefInstantiation, StructDefInstantiationIndex, StructDefinition,
        StructDefinitionIndex, StructFieldInformation, StructHandle, StructHandleIndex,
        StructTypeParameter, TypeSignature, Visibility::*,
    },
};
use move_bytecode_verifier::{verify_module, VerifierConfig};
use move_core_types::{
    account_address::AccountAddress,
    identifier::Identifier,
    language_storage::{ModuleId, StructTag, TypeTag},
    vm_status::StatusCode,
};
use move_vm_runtime::{
    config::VMConfig,
    move_vm::MoveVM,
    session::{SerializedReturnValues, Session},
};
use move_vm_test_utils::{
    gas_schedule::{Gas, GasStatus, INITIAL_COST_SCHEDULE},
    InMemoryStorage,
};
use once_cell::sync::Lazy;
use std::time::Instant;

const MODULE_NAME: &str = "Mod";
const OUTER_NAME: &str = "Outer";
const INNER_NAME: &str = "Inner";
const FIELD_NAME: &str = "inner";
const ENTRY_POINT_NAME_1: &str = "entry_point";
const ENTRY_POINT_NAME_2: &str = "entry_point_one_ty_arg";
const ENTRY_POINT_NAME_3: &str = "entry_point_mul_ty_args";

const RECURSIVE_NAME: &str = "recursive";
const EMPTY_NAME: &str = "empty";

static DEFAULT_SIGNATURES: Lazy<Vec<Signature>> =
    Lazy::new(|| vec![Signature(vec![]), Signature(vec![TypeParameter(0)])]);

#[test]
fn test_limit_pack_unpack() {
    let verifier = VerifierConfig {
        max_type_instantiation_size: Some(128),
        ..Default::default()
    };
    let res = run_with_module(&verifier, pack_unpack_instantiated_1_node);
    res.expect("max_type_instantiation_size(128) pack_unpack_instantiated_1_node failed");
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_3_nodes);
    res.expect(
        "max_type_instantiation_size(128) pack_unpack_instantiated_outer_inner_3_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_5_nodes);
    res.expect(
        "max_type_instantiation_size(128) pack_unpack_instantiated_outer_inner_5_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_51_nodes);
    res.expect(
        "max_type_instantiation_size(128) pack_unpack_instantiated_outer_inner_51_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_1_node);
    res.expect("max_type_instantiation_size(128) pack_unpack_single_type_arg_1_node failed");
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_3_nodes);
    res.expect(
        "max_type_instantiation_size(128) pack_unpack_single_type_arg_outer_inner_3_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_5_nodes);
    res.expect(
        "max_type_instantiation_size(128) pack_unpack_single_type_arg_outer_inner_5_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_51_nodes);
    res.expect(
        "max_type_instantiation_size(128) pack_unpack_single_type_arg_outer_inner_51_nodes failed",
    );

    let verifier = VerifierConfig {
        max_type_instantiation_size: Some(60),
        ..Default::default()
    };
    let res = run_with_module(&verifier, pack_unpack_instantiated_1_node);
    res.expect("max_type_instantiation_size(60) pack_unpack_instantiated_1_node failed");
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_3_nodes);
    res.expect(
        "max_type_instantiation_size(60) pack_unpack_instantiated_outer_inner_3_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_5_nodes);
    res.expect(
        "max_type_instantiation_size(60) pack_unpack_instantiated_outer_inner_5_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_51_nodes);
    res.expect(
        "max_type_instantiation_size(60) pack_unpack_instantiated_outer_inner_51_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_1_node);
    res.expect("max_type_instantiation_size(60) pack_unpack_single_type_arg_1_node failed");
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_3_nodes);
    res.expect(
        "max_type_instantiation_size(60) pack_unpack_single_type_arg_outer_inner_3_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_5_nodes);
    res.expect(
        "max_type_instantiation_size(60) pack_unpack_single_type_arg_outer_inner_5_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_51_nodes);
    res.expect(
        "max_type_instantiation_size(60) pack_unpack_single_type_arg_outer_inner_51_nodes failed",
    );

    let verifier = VerifierConfig {
        max_type_instantiation_size: Some(52),
        ..Default::default()
    };
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_51_nodes);
    res.expect(
        "max_type_instantiation_size(52) pack_unpack_instantiated_outer_inner_51_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_51_nodes);
    res.expect(
        "max_type_instantiation_size(52) pack_unpack_single_type_arg_outer_inner_51_nodes failed",
    );

    let verifier = VerifierConfig {
        max_type_instantiation_size: Some(51),
        ..Default::default()
    };
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_51_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(51) pack_unpack_instantiated_outer_inner_51_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_51_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(51) pack_unpack_single_type_arg_outer_inner_51_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);

    let verifier = VerifierConfig {
        max_type_instantiation_size: Some(50),
        ..Default::default()
    };
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_51_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(50) pack_unpack_instantiated_outer_inner_51_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_51_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(50) pack_unpack_single_type_arg_outer_inner_51_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);

    let verifier = VerifierConfig {
        max_type_instantiation_size: Some(3),
        ..Default::default()
    };
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_5_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(3) pack_unpack_instantiated_outer_inner_5_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_51_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(3) pack_unpack_instantiated_outer_inner_51_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_3_nodes);
    res.expect(
        "max_type_instantiation_size(3) pack_unpack_instantiated_outer_inner_3_nodes failed",
    );
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_5_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(3) pack_unpack_single_type_arg_outer_inner_5_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_51_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(3) pack_unpack_single_type_arg_outer_inner_51_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
    let res = run_with_module(&verifier, pack_unpack_single_type_arg_outer_inner_3_nodes);
    res.expect(
        "max_type_instantiation_size(3) pack_unpack_single_type_arg_outer_inner_3_nodes failed",
    );

    let verifier = VerifierConfig {
        max_type_instantiation_size: Some(2),
        ..Default::default()
    };
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_5_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(2) pack_unpack_instantiated_outer_inner_5_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
    let res = run_with_module(&verifier, pack_unpack_instantiated_outer_inner_3_nodes);
    let err = res.expect_err(
        "max_type_instantiation_size(2) pack_unpack_instantiated_outer_inner_3_nodes must fail",
    );
    assert_eq!(err.major_status(), StatusCode::VERIFICATION_ERROR);
}

// Generate a verifiable module with code that can be used to test instantiations.
// The code is generated by the different tests.
// Provide 2 structs and 3 functions and allow customization of structs and functions
// to test instantiations.
// The 2 structs have the following shape
// struct Outer { inner: vector<Inner> }
// struct Inner<X, Y, .., Z> { field1: X, field2: Y, ..., field(n): Z }
// so that an instance of the Outer struct can be created with an empty vector
// and tests for complex instantiation can be built.
// The number of type parameters for Inner is defined by `struct_type_args_count`.
// The 3 functions have the following signature
// fun entry_point() { ... }
// fun entry_point_one_ty_arg<T>() { ... }
// fun entry_point_mul_ty_args<X, Y, ..., Z>() { ... }
// The number of type parameters for entry_point_mul_ty_args is defined by `fun_type_args_count`.
// Definitions for the 3 functions is provided via `acquires` and `code`, where the content
// of each function is provided in inverse order, so
// [entry_point_mul_ty_args, entry_point_one_ty_arg, entry_point].
// Other aspects of the module are defined in the arguments following `code`.
//
// Please see usage in test to familiarize with how this function is used.
fn make_module(
    session: &mut Session<InMemoryStorage>,
    addr: AccountAddress,
    struct_type_args_count: usize,
    fun_type_args_count: usize,
    mut acquires: Vec<Vec<StructDefinitionIndex>>,
    mut code: Vec<Vec<Bytecode>>,
    mut code_inst_signatures: Vec<Signature>,
    struct_def_instantiations: Vec<StructDefInstantiation>,
) -> ModuleId {
    // default signatures
    let mut signatures = DEFAULT_SIGNATURES.clone();
    signatures.append(&mut code_inst_signatures);
    // default identifiers
    let mut identifiers = vec![
        Identifier::new(MODULE_NAME).unwrap(),
        Identifier::new(OUTER_NAME).unwrap(),
        Identifier::new(INNER_NAME).unwrap(),
        Identifier::new(FIELD_NAME).unwrap(),
        Identifier::new(ENTRY_POINT_NAME_1).unwrap(),
        Identifier::new(ENTRY_POINT_NAME_2).unwrap(),
        Identifier::new(ENTRY_POINT_NAME_3).unwrap(),
    ];

    // define one field for each generic parameter, e.g.
    // struct S<T, W> { field_0: T, field_1: W }
    let mut field_defs = vec![];
    for idx in 0..struct_type_args_count {
        identifiers.push(Identifier::new(format!("field_{}", idx).as_str()).unwrap());
        let id_idx = identifiers.len() - 1;
        field_defs.push(FieldDefinition {
            name: IdentifierIndex(id_idx as u16),
            signature: TypeSignature(TypeParameter(idx as u16)),
        });
    }
    let fields = StructFieldInformation::Declared(field_defs);

    let function_instantiations = vec![];

    let module = CompiledModule {
        version: 6,
        // Module definition
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        // struct definition
        struct_handles: vec![
            StructHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(1),
                abilities: AbilitySet::ALL,
                type_parameters: vec![StructTypeParameter {
                    constraints: AbilitySet::EMPTY,
                    is_phantom: false,
                }],
            },
            StructHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                abilities: AbilitySet::ALL,
                type_parameters: vec![
                    StructTypeParameter {
                        constraints: AbilitySet::EMPTY,
                        is_phantom: false,
                    };
                    struct_type_args_count
                ],
            },
        ],
        struct_defs: vec![
            // struct Outer<T> { inner: vector<T>; }
            // defines a struct that mimics an `Option` field.
            // It allows for the easy creation of complex generic instance without
            // having to build the instance. E.g.
            // struct Outer<Inner<Inner<vector<Inner<vector<.....>>> and so
            // let outer = Outer { inner: vector[], };
            // move_to<...>(addr, outer); // or other bytecodes
            // which results in the ability to test different instantiations at runtime
            StructDefinition {
                struct_handle: StructHandleIndex(0),
                field_information: StructFieldInformation::Declared(vec![FieldDefinition {
                    name: IdentifierIndex(3),
                    signature: TypeSignature(Vector(Box::new(TypeParameter(0)))),
                }]),
            },
            // struct Inner<T, W, ..., Z> { field1: T field2: W, ..., field3: Z; }
            // allows checks of field instantiations instructions
            StructDefinition {
                struct_handle: StructHandleIndex(1),
                field_information: fields,
            },
        ],
        // function definition
        function_handles: vec![
            // fun entry_point()
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(4),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
            // fun entry_point_one_ty_arg<T>()
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(5),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![AbilitySet::VECTOR],
            },
            // fun entry_point_mul_ty_args<X, Y, ..., Z>()
            // for `fun_type_args_count` args
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(6),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![AbilitySet::VECTOR; fun_type_args_count],
            },
        ],
        function_defs: vec![
            FunctionDefinition {
                function: FunctionHandleIndex(0),
                visibility: Public,
                is_entry: true,
                acquires_global_resources: acquires.pop().unwrap(),
                code: Some(CodeUnit {
                    locals: SignatureIndex(0),
                    code: code.pop().unwrap(),
                }),
            },
            FunctionDefinition {
                function: FunctionHandleIndex(1),
                visibility: Public,
                is_entry: true,
                acquires_global_resources: acquires.pop().unwrap(),
                code: Some(CodeUnit {
                    locals: SignatureIndex(0),
                    code: code.pop().unwrap(),
                }),
            },
            FunctionDefinition {
                function: FunctionHandleIndex(2),
                visibility: Public,
                is_entry: true,
                acquires_global_resources: acquires.pop().unwrap(),
                code: Some(CodeUnit {
                    locals: SignatureIndex(0),
                    code: code.pop().unwrap(),
                }),
            },
        ],
        // addresses
        address_identifiers: vec![addr],
        // identifiers
        identifiers,
        // constants
        constant_pool: vec![Constant {
            type_: Address,
            data: addr.to_vec(),
        }],
        // signatures
        signatures,
        // struct instantiations
        struct_def_instantiations,
        // function instantiations
        function_instantiations,
        // unused...
        field_handles: vec![],
        friend_decls: vec![],
        field_instantiations: vec![],
        metadata: vec![],
    };
    // uncomment to see the module generated
    // println!("Module: {:#?}", module);
    verify_module(&module).expect("verification must succeed");

    let mut mod_bytes = vec![];
    module
        .serialize(&mut mod_bytes)
        .expect("Module must serialize");
    session
        .publish_module(mod_bytes, addr, &mut GasStatus::new_unmetered())
        .expect("Module must publish");
    module.self_id()
}

// Generic function to run some code. Take few arguments and a closure
// that can return an entry point to call.
// This function creates a VM, invokes the closure, and on return it builds the call
// for the entry point.
fn run_with_module(
    verifier: &VerifierConfig,
    entry_spec: fn(
        AccountAddress,
        &mut Session<InMemoryStorage>,
    ) -> (ModuleId, Identifier, Vec<TypeTag>),
) -> VMResult<SerializedReturnValues> {
    let addr = AccountAddress::from_hex_literal("0xcafe").unwrap();

    let vm = MoveVM::new_with_config(
        vec![],
        VMConfig {
            verifier: verifier.clone(),
            ..Default::default()
        },
    )
    .unwrap();
    let storage: InMemoryStorage = InMemoryStorage::new();
    let mut session = vm.new_session(&storage);

    let (module_id, entry_name, type_args) = entry_spec(addr, &mut session);

    let mut gas = GasStatus::new_unmetered();
    session.execute_entry_function(
        &module_id,
        entry_name.as_ref(),
        type_args,
        Vec::<Vec<u8>>::new(),
        &mut gas,
    )
}

//
// PackGeneric/UnpackGeneric tests
//

fn get_pack_unpack(sig_idx: usize) -> Vec<Bytecode> {
    let code = vec![
        VecPack(SignatureIndex(sig_idx as u16), 0),
        PackGeneric(StructDefInstantiationIndex(0)),
        UnpackGeneric(StructDefInstantiationIndex(0)),
        Pop,
        Ret,
    ];
    code
}

fn pack_unpack_instantiated_1_node(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let code_inst_signatures = vec![Signature(vec![U128])];
    pack_instantiated(addr, session, code_inst_signatures)
}

fn pack_unpack_instantiated_outer_inner_3_nodes(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let code_inst_signatures = vec![Signature(vec![StructInstantiation(
        StructHandleIndex(1),
        vec![U128],
    )])];
    pack_instantiated(addr, session, code_inst_signatures)
}

fn pack_unpack_instantiated_outer_inner_5_nodes(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let instantiation = StructInstantiation(
        StructHandleIndex(1),
        vec![Vector(Box::new(StructInstantiation(
            StructHandleIndex(1),
            vec![Bool],
        )))],
    );
    let code_inst_signatures = vec![Signature(vec![instantiation])];
    pack_instantiated(addr, session, code_inst_signatures)
}

fn pack_unpack_instantiated_outer_inner_51_nodes(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let mut instantiation = vec![Bool];
    for _ in 0..50 {
        instantiation = vec![StructInstantiation(StructHandleIndex(1), instantiation)];
    }
    let code_inst_signatures = vec![Signature(instantiation)];
    pack_instantiated(addr, session, code_inst_signatures)
}

fn pack_instantiated(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
    code_inst_signatures: Vec<Signature>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    //
    // Module definition and publishing
    let struct_type_args_count = 1;
    let fun_type_args_count = 0;
    let sig_start = DEFAULT_SIGNATURES.len();
    let struct_def_instantiations = vec![StructDefInstantiation {
        def: StructDefinitionIndex(0),
        type_parameters: SignatureIndex(sig_start as u16),
    }];

    let code = get_pack_unpack(sig_start);
    let acquires = vec![vec![], vec![], vec![]];
    let code = vec![vec![Ret], vec![Ret], code];

    let self_id = make_module(
        session,
        addr,
        struct_type_args_count,
        fun_type_args_count,
        acquires,
        code,
        code_inst_signatures,
        struct_def_instantiations,
    );

    //
    // Entry specification
    (
        self_id,
        Identifier::new(ENTRY_POINT_NAME_1).unwrap(),
        vec![],
    )
}

fn pack_unpack_single_type_arg_1_node(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let (module_id, entry_fn) = pack_single_type_arg(addr, session, vec![]);
    (module_id, entry_fn, vec![TypeTag::U128])
}

fn pack_unpack_single_type_arg_outer_inner_3_nodes(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let (module_id, entry_fn) = pack_single_type_arg(addr, session, vec![]);
    let ty_arg = TypeTag::Struct(Box::new(StructTag {
        address: addr,
        module: Identifier::new(MODULE_NAME).unwrap(),
        name: Identifier::new(INNER_NAME).unwrap(),
        type_params: vec![TypeTag::Address],
    }));
    (module_id, entry_fn, vec![ty_arg])
}

fn pack_unpack_single_type_arg_outer_inner_5_nodes(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let (module_id, entry_fn) = pack_single_type_arg(addr, session, vec![]);
    let ty_arg = TypeTag::Struct(Box::new(StructTag {
        address: addr,
        module: Identifier::new(MODULE_NAME).unwrap(),
        name: Identifier::new(INNER_NAME).unwrap(),
        type_params: vec![TypeTag::Vector(Box::new(TypeTag::Struct(Box::new(
            StructTag {
                address: addr,
                module: Identifier::new(MODULE_NAME).unwrap(),
                name: Identifier::new(INNER_NAME).unwrap(),
                type_params: vec![TypeTag::U64],
            },
        ))))],
    }));
    (module_id, entry_fn, vec![ty_arg])
}

fn pack_unpack_single_type_arg_outer_inner_51_nodes(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
) -> (ModuleId, Identifier, Vec<TypeTag>) {
    let (module_id, entry_fn) = pack_single_type_arg(addr, session, vec![]);
    let mut ty_arg = TypeTag::U128;
    for _ in 0..50 {
        ty_arg = TypeTag::Struct(Box::new(StructTag {
            address: addr,
            module: Identifier::new(MODULE_NAME).unwrap(),
            name: Identifier::new(INNER_NAME).unwrap(),
            type_params: vec![ty_arg],
        }));
    }
    (module_id, entry_fn, vec![ty_arg])
}

fn pack_single_type_arg(
    addr: AccountAddress,
    session: &mut Session<InMemoryStorage>,
    code_inst_signatures: Vec<Signature>,
) -> (ModuleId, Identifier) {
    //
    // Module definition and publishing
    let struct_type_args_count = 1;
    let fun_type_args_count = 1;
    let struct_def_instantiations = vec![StructDefInstantiation {
        def: StructDefinitionIndex(0),
        type_parameters: SignatureIndex(1),
    }];

    let code = get_pack_unpack(1);
    let acquires = vec![vec![], vec![], vec![]];
    let code = vec![vec![Ret], code, vec![Ret]];

    let self_id = make_module(
        session,
        addr,
        struct_type_args_count,
        fun_type_args_count,
        acquires,
        code,
        code_inst_signatures,
        struct_def_instantiations,
    );

    //
    // Entry specification
    (self_id, Identifier::new(ENTRY_POINT_NAME_2).unwrap())
}
