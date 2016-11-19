import com.mysql.jdbc.exceptions.MySQLIntegrityConstraintViolationException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.DefaultCellEditor;
import javax.swing.JComboBox;
import javax.swing.JOptionPane;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableColumn;

/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author vlad
 */
public class laba3 extends javax.swing.JFrame {

    /**
     * Creates new form laba3
     */
    public laba3() {
        initComponents();
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jTabbedPane = new javax.swing.JTabbedPane();
        jScrollPaneData = new javax.swing.JScrollPane();
        jTableData = new javax.swing.JTable();
        jScrollPanePublishing = new javax.swing.JScrollPane();
        jTablePublishing = new javax.swing.JTable();
        jScrollPaneCities = new javax.swing.JScrollPane();
        jTableCities = new javax.swing.JTable();
        jButtonAdd = new javax.swing.JButton();
        jButtonDelete = new javax.swing.JButton();
        jButtonUpdateTables = new javax.swing.JButton();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);
        setTitle("Lab 3. Library. Beklenyshchev Vladislav. PK-12-2. DNU. 2016");
        setLocation(new java.awt.Point(250, 100));

        jTableData.setModel(new javax.swing.table.DefaultTableModel(
            new Object [][] {
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null},
                {null, null, null, null, null, null}
            },
            new String [] {
                "Book", "Author", "Year", "Publishing house", "Price", "Count of books"
            }
        ) {
            Class[] types = new Class [] {
                java.lang.String.class, java.lang.String.class, java.lang.String.class, java.lang.String.class, java.lang.String.class, java.lang.String.class
            };

            public Class getColumnClass(int columnIndex) {
                return types [columnIndex];
            }
        });
        jScrollPaneData.setViewportView(jTableData);

        jTabbedPane.addTab("Data", jScrollPaneData);

        jTablePublishing.setModel(new javax.swing.table.DefaultTableModel(
            new Object [][] {
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null},
                {null, null, null, null}
            },
            new String [] {
                "Publishing", "Country", "City", "Phone"
            }
        ) {
            Class[] types = new Class [] {
                java.lang.String.class, java.lang.String.class, java.lang.String.class, java.lang.String.class
            };

            public Class getColumnClass(int columnIndex) {
                return types [columnIndex];
            }
        });
        jTablePublishing.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                jTablePublishingMouseClicked(evt);
            }
        });
        jScrollPanePublishing.setViewportView(jTablePublishing);

        jTabbedPane.addTab("About publishing", jScrollPanePublishing);

        jTableCities.setModel(new javax.swing.table.DefaultTableModel(
            new Object [][] {
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null},
                {null, null}
            },
            new String [] {
                "City", "Country"
            }
        ) {
            Class[] types = new Class [] {
                java.lang.String.class, java.lang.String.class
            };

            public Class getColumnClass(int columnIndex) {
                return types [columnIndex];
            }
        });
        jScrollPaneCities.setViewportView(jTableCities);

        jTabbedPane.addTab("Directory of cities", jScrollPaneCities);

        jButtonAdd.setText("Add");
        jButtonAdd.setEnabled(false);
        jButtonAdd.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                jButtonAddActionPerformed(evt);
            }
        });

        jButtonDelete.setText("Delete");
        jButtonDelete.setEnabled(false);
        jButtonDelete.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                jButtonDeleteActionPerformed(evt);
            }
        });

        jButtonUpdateTables.setText("Update tables");
        jButtonUpdateTables.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                jButtonUpdateTablesActionPerformed(evt);
            }
        });

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(layout.createSequentialGroup()
                        .addComponent(jButtonUpdateTables, javax.swing.GroupLayout.PREFERRED_SIZE, 120, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addGap(18, 18, 18)
                        .addComponent(jButtonAdd, javax.swing.GroupLayout.PREFERRED_SIZE, 120, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addGap(18, 18, 18)
                        .addComponent(jButtonDelete, javax.swing.GroupLayout.PREFERRED_SIZE, 120, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addGap(0, 0, Short.MAX_VALUE))
                    .addComponent(jTabbedPane, javax.swing.GroupLayout.DEFAULT_SIZE, 775, Short.MAX_VALUE))
                .addContainerGap())
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(jTabbedPane, javax.swing.GroupLayout.PREFERRED_SIZE, 218, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(jButtonDelete, javax.swing.GroupLayout.PREFERRED_SIZE, 40, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(jButtonAdd, javax.swing.GroupLayout.PREFERRED_SIZE, 40, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(jButtonUpdateTables, javax.swing.GroupLayout.PREFERRED_SIZE, 40, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addContainerGap())
        );

        pack();
    }// </editor-fold>//GEN-END:initComponents

    private void jButtonUpdateTablesActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_jButtonUpdateTablesActionPerformed
        // TODO add your handling code here:
        
        // clear all tables
        DefaultTableModel modelData = (DefaultTableModel) jTableData.getModel();
        modelData.setRowCount(0);
        modelData.setRowCount(20);
        DefaultTableModel modelPublishing = (DefaultTableModel) jTablePublishing.getModel();
        modelPublishing.setRowCount(0);
        modelPublishing.setRowCount(20);
        DefaultTableModel modelCities = (DefaultTableModel) jTableCities.getModel();
        modelCities.setRowCount(0);
        modelCities.setRowCount(20);
        JavaToMySQL jdbcConnection = new JavaToMySQL();
        Connection connection = jdbcConnection.Connect();
        // select all rows from all tables
            Statement statement = null;
            try {
                statement = connection.createStatement();
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            String selectFromTableDataSQL = "SELECT * FROM data";
            ResultSet gotData = null;
            try {
                gotData = statement.executeQuery(selectFromTableDataSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            try {
                for(int i = 0;gotData.next(); i++){
                    ArrayList<Object> dataRow = new ArrayList<Object>();
                    dataRow.add(gotData.getObject("book_name"));
                    dataRow.add(gotData.getObject("author"));
                    dataRow.add(gotData.getObject("publishing_year"));
                    dataRow.add(gotData.getObject("publishing_house"));
                    dataRow.add(gotData.getObject("price"));
                    dataRow.add(gotData.getObject("count_of_books"));
                    // loop for rows of jTableData
                    for(int j = 0; j < jTableData.getColumnCount();j++){
                        jTableData.setValueAt(dataRow.get(j), i, j);
                    }
                }
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            
            
            /////// about_publishing
            selectFromTableDataSQL = "SELECT * FROM about_publishing";
            gotData = null;
            try {
                gotData = statement.executeQuery(selectFromTableDataSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            try {
                for(int i = 0;gotData.next(); i++){
                    ArrayList<Object> dataRow = new ArrayList<Object>();
                    dataRow.add(gotData.getObject("publishing_house"));
                    dataRow.add(gotData.getObject("country"));
                    dataRow.add(gotData.getObject("city"));
                    dataRow.add(gotData.getObject("phone"));
                    // loop for rows of jTableData
                    for(int j = 0; j < jTablePublishing.getColumnCount();j++){
                        jTablePublishing.setValueAt(dataRow.get(j), i, j);
                    }
                }
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            
            
            /////// cities
            
            selectFromTableDataSQL = "SELECT * FROM directory_of_cities";
            gotData = null;
            try {
                gotData = statement.executeQuery(selectFromTableDataSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            try {
                for(int i = 0;gotData.next(); i++){
                    ArrayList<Object> dataRow = new ArrayList<Object>();
                    dataRow.add(gotData.getObject("city"));
                    dataRow.add(gotData.getObject("country"));
                    // loop for rows of jTableData
                    for(int j = 0; j < jTableCities.getColumnCount();j++){
                        jTableCities.setValueAt(dataRow.get(j), i, j);
                    }
                }
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            
            
            try {
                connection.close();
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
                //return null;
            }
            
            jButtonAdd.setEnabled(true);
            jButtonDelete.setEnabled(true);
    }//GEN-LAST:event_jButtonUpdateTablesActionPerformed

    private void jButtonAddActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_jButtonAddActionPerformed
        // TODO add your handling code here:
        JavaToMySQL jdbcConnection = new JavaToMySQL();
        Connection connection = jdbcConnection.Connect();
        // select all rows from all tables
            Statement statement = null;
            try {
                statement = connection.createStatement();
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
        
        if(jTabbedPane.getSelectedIndex() == 0){
            int idRow = jTableData.getSelectedRow();
            ArrayList<Object> dataList = new ArrayList<Object>();
            for(int i = 0; i< jTableData.getColumnCount(); i++){
                dataList.add(jTableData.getValueAt(idRow, i));
            }
            
            String insertTableSQL = "INSERT INTO data"
            + "(book_name, author, publishing_year, publishing_house, price, count_of_books) " 
                    + "VALUES ('"+dataList.get(0)+"','"+dataList.get(1)+"','"+dataList.get(2)+"','"
                    +dataList.get(3)+"','"+dataList.get(4)+"','"+dataList.get(5)+"')";
            try {
                statement.execute(insertTableSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        else if(jTabbedPane.getSelectedIndex() == 1){
            int idRow = jTablePublishing.getSelectedRow();
            ArrayList<Object> dataList = new ArrayList<Object>();
            for(int i = 0; i< jTablePublishing.getColumnCount(); i++){
                dataList.add(jTablePublishing.getValueAt(idRow, i));
            }
            
            
            try {
                statement = connection.createStatement();
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            String selectFromTableDataSQL = "SELECT city FROM directory_of_cities";
            ResultSet gotData = null;
            try {
                gotData = statement.executeQuery(selectFromTableDataSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            
            boolean isCityExist = false;
            try {
                for(;gotData.next();){
                    if(gotData.getObject("city").equals(dataList.get(2))){
                        isCityExist = true;
                    }
                }
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
            
            if(isCityExist){
                    String insertTableSQL = "INSERT INTO about_publishing"
                + "(publishing_house, country, city, phone) " 
                        + "VALUES ('"+dataList.get(0)+"','"+dataList.get(1)+"','"+dataList.get(2)+"','"
                        +dataList.get(3)+"')";
                try {
                    statement.execute(insertTableSQL);
                } catch (SQLException ex) {
                    Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
                }
            }
            else{
                JOptionPane.showMessageDialog(null, "City " + dataList.get(2) 
                + " isn't exist in Data Base. Try check table 'Directory of cities.'");
            }
            
        }
        else if(jTabbedPane.getSelectedIndex() == 2){
            int idRow = jTableCities.getSelectedRow();
            ArrayList<Object> dataList = new ArrayList<Object>();
            for(int i = 0; i< jTableCities.getColumnCount(); i++){
                dataList.add(jTableCities.getValueAt(idRow, i));
            }
            
            String insertTableSQL = "INSERT INTO directory_of_cities"
            + "(city, country) " 
                    + "VALUES ('"+dataList.get(0)+"','"+dataList.get(1)+"')";
            try {
                statement.execute(insertTableSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        
         try {
                connection.close();
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
                //return null;
            }
    }//GEN-LAST:event_jButtonAddActionPerformed

    private void jButtonDeleteActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_jButtonDeleteActionPerformed
        // TODO add your handling code here:
        // TODO add your handling code here:
        JavaToMySQL jdbcConnection = new JavaToMySQL();
        Connection connection = jdbcConnection.Connect();
        // select all rows from all tables
            Statement statement = null;
            try {
                statement = connection.createStatement();
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
        
        if(jTabbedPane.getSelectedIndex() == 0){
            int idRow = jTableData.getSelectedRow();
            String sBookName = (String)jTableData.getValueAt(idRow, 0);
            
            String insertTableSQL = "DELETE FROM data WHERE "
            + "book_name = '"+ sBookName +"'";
            try {
                statement.execute(insertTableSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        else if(jTabbedPane.getSelectedIndex() == 1){
            int idRow = jTablePublishing.getSelectedRow();
            String sPublishing = (String)jTablePublishing.getValueAt(idRow, 0);
            
            String insertTableSQL = "DELETE FROM about_publishing WHERE "
            + "publishing_house = '"+ sPublishing +"'";
            try {
                statement.execute(insertTableSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        else if(jTabbedPane.getSelectedIndex() == 2){
            int idRow = jTableCities.getSelectedRow();
            String sCity = (String)jTableCities.getValueAt(idRow, 0);
            
            String insertTableSQL = "DELETE FROM directory_of_cities WHERE "
            + "city = '"+ sCity +"'";
            try {
                statement.execute(insertTableSQL);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
            }
        }
        
         try {
                connection.close();
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
                //return null;
            }
    }//GEN-LAST:event_jButtonDeleteActionPerformed

    private void jTablePublishingMouseClicked(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_jTablePublishingMouseClicked
        // TODO add your handling code here:
        
    }//GEN-LAST:event_jTablePublishingMouseClicked

    class JavaToMySQL{
        private String url = "jdbc:mysql://localhost:3306/library";
        private String username = "root";
        private String password = "2394";
        
        JavaToMySQL(){
        }
                
        public Connection Connect(){
            try{
                Class.forName("com.mysql.jdbc.Driver");
            }
            catch(ClassNotFoundException ex){
                 System.out.println("Where is your MySQL JDBC Driver?");
                 ex.printStackTrace();
                 return null;
            }
            Connection conn = null;
            try {
                conn = DriverManager.getConnection(url, username, password);
            } catch (SQLException ex) {
                Logger.getLogger(laba3.class.getName()).log(Level.SEVERE, null, ex);
                return null;
            }
            
            
           
            return conn;
        }
    }
    
    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        /* Set the Nimbus look and feel */
        //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
        /* If Nimbus (introduced in Java SE 6) is not available, stay with the default look and feel.
         * For details see http://download.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html 
         */
        try {
            for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
                if ("Nimbus".equals(info.getName())) {
                    javax.swing.UIManager.setLookAndFeel(info.getClassName());
                    break;
                }
            }
        } catch (ClassNotFoundException ex) {
            java.util.logging.Logger.getLogger(laba3.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(laba3.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(laba3.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(laba3.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>
        
        /* Create and display the form */
        java.awt.EventQueue.invokeLater(new Runnable() {
            public void run() {
                new laba3().setVisible(true);
            }
        });
    }

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton jButtonAdd;
    private javax.swing.JButton jButtonDelete;
    private javax.swing.JButton jButtonUpdateTables;
    private javax.swing.JScrollPane jScrollPaneCities;
    private javax.swing.JScrollPane jScrollPaneData;
    private javax.swing.JScrollPane jScrollPanePublishing;
    private javax.swing.JTabbedPane jTabbedPane;
    private javax.swing.JTable jTableCities;
    private javax.swing.JTable jTableData;
    private javax.swing.JTable jTablePublishing;
    // End of variables declaration//GEN-END:variables
}