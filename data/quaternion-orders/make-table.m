
db.create_table?

Let’s give the example of making a database of polarized quaternion orders:

this makes the columns and the type in postgres
label ? order_label ? mu ? deg_mu ? nrd_mu ? AutmuO_size ? AutmuO_label ? AutmuO_is_cyclic ? AutmuO_generators ? Gerby_gen 
text ? text ? integer[] ? integer ? integer ? integer ? text ? boolean ? integer[] ? integer[]

search_cols = {'text' : ['label','order_label','AutmuO_label'], 'integer': ['deg_mu','nrd_mu','AutmuO_size'], 'integer[]': ['mu','AutmuO_generators','Gerby_gen'], 'boolean':['AutmuO_is_cyclic']}
 
these are the descriptions of the columns
col_desc = {
 'label': 'the label of the polarized quaternion order, of the format discB.discO.deg_mu or just discO.deg_mu if O is maximal',
 'order_label': 'the label of the quaternion order',
 'mu': 'the polarized element mu, written in terms of the basis of O',
 'deg_mu': 'the degree of the polarized element mu',
 'nrd_mu': 'the reduced norm of the polarized element mu',
 'AutmuO_size': 'the size of AutmuO',
 'AutmuO_label': 'the group label of AutmuO',
 'AutmuO_is_cyclic': 'whether AutmuO is cyclic',
 'AutmuO_generators': 'generators of AutmuO, written in terms of the basis of O',
 'Gerby_gen': 'generators of the kernel of the full enhanced semidirect product acting on the upper and lowe half plane' }

now we can create the table
db.create_table('quaternion_orders_polarized', search_columns = search_cols, label_col = 'label', table_description = 'a table of polarized quaternion orders', col_description = col_desc)

now copy the file from somewhere with the data which must be in the correct format for postgres to work with it and the table to accept it.
db.quaternion_orders_polarized.copy_from('../ShimCurve/data/quaternion-orders/quaternion-orders-polarized.m', sep='?')
db.quaternion_orders.copy_from('../ShimCurve/data/quaternion-orders/quaternion-orders.m', sep='?')

