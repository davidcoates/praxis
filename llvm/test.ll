declare i8* @malloc(i32)
declare void @free(i8*)
declare i32 @printf(i8*, ...)

%fn_capture_type = type { i64, ptr }

%fn_type = type { ptr, ptr }

%lambda_capture_type = type { %fn_capture_type, i32 }

define i32 @lambda_impl(ptr %capture, i32 %x) {
  %1 = getelementptr %lambda_capture_type, ptr %capture, i32 0, i32 1
  %y = load i32, ptr %1
  %2 = add i32 %y, %x
  ret i32 %2
}

define %fn_type @copy_fn(%fn_type %fn) alwaysinline {
  %fn_capture_ptr = extractvalue %fn_type %fn, 1
  %1 = icmp eq ptr %fn_capture_ptr, null
  br i1 %1, label %b_no_captures, label %b_captures
b_no_captures:
  ret %fn_type %fn
b_captures:
  %ref_count_ptr = getelementptr %fn_capture_type, ptr %fn_capture_ptr, i32 0, i32 0
  %old_ref_count = load i64, ptr %ref_count_ptr
  %new_ref_count = add i64 %old_ref_count, 1
  store i64 %new_ref_count, ptr %ref_count_ptr
  ret %fn_type %fn
}

define void @dispose_fn(%fn_type %fn) {
  %fn_capture_ptr = extractvalue %fn_type %fn, 1
  %1 = icmp eq ptr %fn_capture_ptr, null
  br i1 %1, label %b_no_captures, label %b_captures
b_no_captures:
  ret void
b_captures:
  %ref_count_ptr = getelementptr %fn_capture_type, ptr %fn_capture_ptr, i32 0, i32 0
  %old_ref_count = load i64, ptr %ref_count_ptr
  %2 = icmp eq i64 %old_ref_count, 1
  br i1 %2, label %b_last_ref, label %b_not_last_ref
b_last_ref:
  %dispose_ptr = getelementptr %fn_capture_type, ptr %fn_capture_ptr, i32 0, i32 1
  %dispose_fn = load ptr, ptr %dispose_ptr
  %3 = icmp ne ptr %dispose_fn, null
  br i1 %3, label %b_dispose, label %b_no_dispose
b_dispose:
  call void (ptr) %dispose_fn(ptr %fn_capture_ptr)
  call void (i8*) @free(ptr %fn_capture_ptr)
  ret void
b_no_dispose:
  call void (i8*) @free(ptr %fn_capture_ptr)
  ret void
b_not_last_ref:
  %new_ref_count = sub i64 %old_ref_count, 1
  store i64 %new_ref_count, ptr %ref_count_ptr
  ret void
}

define i32 @call_i32_to_i32(%fn_type %fn, i32 %x) {
  %fn_impl_ptr = extractvalue %fn_type %fn, 0
  %fn_capture_ptr = extractvalue %fn_type %fn, 1
  %1 = icmp eq ptr %fn_capture_ptr, null
  br i1 %1, label %b_no_captures, label %b_captures
b_no_captures:
  %2 = call i32(i32) %fn_impl_ptr(i32 %x)
  ret i32 %2
b_captures:
  %3 = call i32(ptr, i32) %fn_impl_ptr(ptr %fn_capture_ptr, i32 %x)
  ret i32 %3
}

define %fn_type @create_lambda(i32 %y) {
  %size = getelementptr [1 x %lambda_capture_type], ptr null, i32 1
  %sizeI = ptrtoint %lambda_capture_type* %size to i32
  %lambda_capture_ptr = call i8* (i32) @malloc(i32 %sizeI)
  %ref_count_ptr = getelementptr %lambda_capture_type, ptr %lambda_capture_ptr, i32 0, i32 0, i32 0
  store i64 1, ptr %ref_count_ptr
  %dispose_ptr = getelementptr %lambda_capture_type, ptr %lambda_capture_ptr, i32 0, i32 0, i32 1
  store ptr null, ptr %dispose_ptr
  %y_ptr = getelementptr %lambda_capture_type, ptr %lambda_capture_ptr, i32 0, i32 1
  store i32 %y, ptr %y_ptr
  %1 = insertvalue %fn_type undef, ptr @lambda_impl, 0
  %2 = insertvalue %fn_type %1, ptr %lambda_capture_ptr, 1
  ret %fn_type %2
}

@.format = private constant [4 x i8] c"%d\0A\00"

define i32 @main() {
  %lambda = call %fn_type (i32) @create_lambda(i32 6)
  %result = call i32 (%fn_type, i32) @call_i32_to_i32(%fn_type %lambda, i32 5)
  call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.format , i32 0, i32 0), i32 %result)
  call void (%fn_type) @dispose_fn(%fn_type %lambda)
  ret i32 0
}

