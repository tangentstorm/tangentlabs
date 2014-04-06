import java.awt.Container;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFrame;


public class JCheckboxDemo {

	private JCheckBox cbClass;
	
	public void swingMain() {
		
		final JCheckBox cbLocal = new JCheckBox("local");
		this.cbClass = new JCheckBox("class");
		
		JButton button = new JButton("print state");
		button.addActionListener(new ActionListener() {
			
			@Override
			public void actionPerformed(ActionEvent e) {
				System.out.print(  "  cbClass.isSelected(): " + cbClass.isSelected());
				System.out.println("  cbLocal.isSelected(): " + cbLocal.isSelected());
			}
		});
		
		
		JFrame frame = new JFrame("JCheckboxDemo");
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		Container p = frame.getContentPane();
		p.setLayout(new FlowLayout());
		p.add(cbLocal);
		p.add(cbClass);
		p.add(button);
		frame.pack();
		frame.setVisible(true);
	}
	
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		javax.swing.SwingUtilities.invokeLater(new Runnable() {
			
			@Override
			public void run() {
				new JCheckboxDemo().swingMain();
			}
		});

	}

}
