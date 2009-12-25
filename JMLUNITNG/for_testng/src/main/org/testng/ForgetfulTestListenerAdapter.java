package org.testng;

import java.util.List;

public class ForgetfulTestListenerAdapter extends TestListenerAdapter {

	private int failed;
	private int passed;
	private int skipped;
	
	public int failed() { return failed; }
	public int passed() { return passed; }
	public int skipped() { return skipped; }
	
	@Override
	public void onConfigurationFailure(ITestResult itr) {
		// TODO Auto-generated method stub
		super.onConfigurationFailure(itr);
	}
	@Override
	public void onConfigurationSkip(ITestResult itr) {
		// TODO Auto-generated method stub
		super.onConfigurationSkip(itr);
	}
	@Override
	public void onConfigurationSuccess(ITestResult itr) {
		// TODO Auto-generated method stub
		super.onConfigurationSuccess(itr);
	}
	@Override
	public void onFinish(ITestContext testContext) {
		// TODO Auto-generated method stub
		super.onFinish(testContext);
	}
	@Override
	public void onStart(ITestContext testContext) {
		// TODO Auto-generated method stub
		super.onStart(testContext);
	}
	@Override
	public void onTestStart(ITestResult result) {
		// TODO Auto-generated method stub
		super.onTestStart(result);
	}
	@Override
	public void setAllTestMethods(List<ITestNGMethod> allTestMethods) {
		// TODO Auto-generated method stub
		super.setAllTestMethods(allTestMethods);
	}
	@Override
	public void setFailedButWithinSuccessPercentageTests(
			List<ITestResult> failedButWithinSuccessPercentageTests) {
		// TODO Auto-generated method stub
		super
				.setFailedButWithinSuccessPercentageTests(failedButWithinSuccessPercentageTests);
	}
	@Override
	public void setFailedTests(List<ITestResult> failedTests) {
		// TODO Auto-generated method stub
		super.setFailedTests(failedTests);
	}
	@Override
	public void setPassedTests(List<ITestResult> passedTests) {
		// TODO Auto-generated method stub
		super.setPassedTests(passedTests);
	}
	@Override
	public void setSkippedTests(List<ITestResult> skippedTests) {
		// TODO Auto-generated method stub
		super.setSkippedTests(skippedTests);
	}
	@Override
	public synchronized void onTestFailedButWithinSuccessPercentage(ITestResult tr) {
		failed++;
	}

	@Override
	public synchronized void onTestFailure(ITestResult tr) {
		failed++;
	}

	@Override
	public synchronized void onTestSkipped(ITestResult tr) {
		skipped++;
	}

	@Override
	public synchronized void onTestSuccess(ITestResult tr) {
		passed++;
	}

}
