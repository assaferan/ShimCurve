procedure TestReset();
  // No shared mutable state; kept for API compatibility.
  return;
end procedure;

procedure TestPass(msg);
  printf "[PASS] %o\n", msg;
end procedure;

procedure TestFail(msg);
  printf "[FAIL] %o\n", msg;
  error Sprintf("Test failed: %o", msg);
end procedure;

procedure TestSkip(msg);
  printf "[SKIP] %o\n", msg;
end procedure;

procedure TestAssert(cond, msg);
  if cond then
    TestPass(msg);
  else
    TestFail(msg);
  end if;
end procedure;

procedure TestAssertEq(lhs, rhs, msg);
  if lhs eq rhs then
    TestPass(msg);
  else
    TestFail(Sprintf("%o (lhs=%o, rhs=%o)", msg, lhs, rhs));
  end if;
end procedure;

function TestFailureCount();
  return 0;
end function;

function TestSkipCount();
  return 0;
end function;
